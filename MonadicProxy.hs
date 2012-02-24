{-# LANGUAGE QuasiQuotes, ViewPatterns #-}
{-# LANGUAGE GADTs, ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}

module Monadic where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity

import Data.Proxy

-- Hobbits-related stuff
import Data.Binding.Hobbits
import qualified Data.Type.List.Map as Map
import Data.Type.List.Proof.Member as Member

import Galois

-- misc stuff
instance Liftable Bool where
    mbLift [nuP| True |] = True
    mbLift [nuP| False |] = False


------------------------------------------------------------
-- Interpreter monad
------------------------------------------------------------

type Env ctx = MapC Identity ctx

--newtype InterpM ctx a = InterpM { unInterpM :: ReaderT (Env ctx) Identity a }
newtype InterpM a = InterpM { unInterpM :: StateT Int Identity a }

instance Monad InterpM where
    return = InterpM . return
    m >>= f = InterpM $ unInterpM m >>= unInterpM . f

instance MonadState Int InterpM where
    get = InterpM get
    put = InterpM . put


------------------------------------------------------------
-- Object language types
------------------------------------------------------------

data Type a where
    Bool :: Type Bool
    Int :: Type Int
    Arrow :: Type a -> Type b -> Type (a -> b)
    M :: Type a -> Type (InterpM a)

class IsType a where
    typeRep :: Type a

instance IsType Bool where
    typeRep = Bool

instance IsType Int where
    typeRep = Int

instance (IsType a, IsType b) => IsType (a -> b) where
    typeRep = Arrow typeRep typeRep

instance IsType a => IsType (InterpM a) where
    typeRep = M typeRep


------------------------------------------------------------
-- Intensional type functions
------------------------------------------------------------

type family Apply f a

newtype ApplyF f a = ApplyF { unApplyF :: Apply f a }


------------------------------------------------------------
-- Interpreter class
------------------------------------------------------------

class Semantics f where
{-
    intLit :: Int -> Apply f Int
    boolLit :: Bool -> Apply f Bool

    lam :: (Apply f a -> Apply f b) -> Apply f (a -> b)
    app :: Apply f (a -> b) -> Apply f a -> Apply f b

    if_ :: Apply f Bool -> Apply f a -> Apply f a -> Apply f a

    lt :: Apply f Int -> Apply f Int -> Apply f Bool
    plus :: Apply f Int -> Apply f Int -> Apply f Int

    ret :: Apply f a -> Apply f (InterpM a)
    bind :: Apply f (InterpM a) -> Apply f (a -> InterpM b) -> Apply f (InterpM b)
    incr :: Apply f (InterpM Int)
-}

    intLit :: Proxy f -> Int -> Apply f Int
    --intLit i = intLitP Proxy i
    boolLit :: Proxy f -> Bool -> Apply f Bool
    --boolLitP _ = boolLit

    lam :: Proxy f -> (Apply f a -> Apply f b) -> Apply f (a -> b)
    --lamP _ = lam

    app :: Proxy f -> Apply f (a -> b) -> Apply f a -> Apply f b
    --appP _ = app

    if_ :: Proxy f -> Apply f Bool -> Apply f a -> Apply f a -> Apply f a
    --if_P _ = if_

    lt :: Proxy f -> Apply f Int -> Apply f Int -> Apply f Bool
    --ltP _ = lt
    plus :: Proxy f -> Apply f Int -> Apply f Int -> Apply f Int
    --plusP _ = plus

    ret :: Proxy f -> Apply f a -> Apply f (InterpM a)
    --retP _ = ret
    bind :: Proxy f -> Apply f (InterpM a) -> Apply f (a -> InterpM b) -> Apply f (InterpM b)
    --bindP _ = bind
    incr :: Proxy f -> Apply f (InterpM Int)
    --incrP _ = incr


------------------------------------------------------------
-- A Simple Interpreter
------------------------------------------------------------

-- Identity type function
data Id
type instance Apply Id a = a

instance Semantics Id where
    intLit _ = id
    boolLit _ = id
    lam _ = id
    app _ = ($)

    if_ _ True x y = x
    if_ _ False x y = y

    lt _ = (<)
    plus _ = (+)

    ret _ = return
    bind _ = (>>=)
    incr _ = modify ((+) 1) >> get


------------------------------------------------------------
-- The "Code" type
------------------------------------------------------------

data Term a where
    IntLit :: Int -> Term Int
    BoolLit :: Bool -> Term Bool

    Var :: Name a -> Term a
    Lam :: Binding a (Term b) -> Term (a -> b)
    App :: Term (a -> b) -> Term a -> Term b

    If :: Term Bool -> Term a -> Term a -> Term a
    Lt :: Term Int -> Term Int -> Term Bool
    Plus :: Term Int -> Term Int -> Term Int

    Ret :: Term a -> Term (InterpM a)
    Bind :: Term (InterpM a) -> Term (a -> InterpM b) -> Term (InterpM b)
    Incr :: Term (InterpM Int)


eval :: Term a -> a
eval t = mbEval Nil (emptyMb t)

mbEval :: MapC Identity ctx -> Mb ctx (Term a) -> a
mbEval env [nuP| IntLit i |] = mbLift i
mbEval env [nuP| BoolLit b |] = mbLift b
mbEval env [nuP| Var x |]
    | Left inCtx <- mbNameBoundP x
    = runIdentity $ Map.lookup inCtx env
mbEval env [nuP| Var x |] = error "Unbound variable!"
mbEval env [nuP| Lam b |] = \x -> mbEval (env :> Identity x) (combineMb b)
mbEval env [nuP| App t1 t2 |] = (mbEval env t1) (mbEval env t2)
mbEval env [nuP| If b t1 t2 |] =
    if mbEval env b then mbEval env t1 else mbEval env t2
mbEval env [nuP| Lt t1 t2 |] = mbEval env t1 < mbEval env t2
mbEval env [nuP| Plus t1 t2 |] = mbEval env t1 + mbEval env t2
mbEval env [nuP| Ret t |] = return $ mbEval env t
mbEval env [nuP| Bind t1 t2 |] = mbEval env t1 >>= mbEval env t2
mbEval env [nuP| Incr |] = modify ((+) 1) >> get


------------------------------------------------------------
-- A Staged Interpreter
------------------------------------------------------------

-- Term type function
data TermF
type instance Apply TermF a = Term a

instance Semantics TermF where
    intLit _ = IntLit
    boolLit _ = BoolLit

    lam _ f = Lam $ nu $ f . Var
    app _ = App

    if_ _ = If

    lt _ = Lt
    plus _ = Plus

    ret _ = Ret
    bind _ = Bind
    incr _ = Incr


------------------------------------------------------------
-- Galois connections over just the object language types
------------------------------------------------------------

class GaloisConnection1F spec impl where
    abstr1f :: Type a -> (Proxy spec, Proxy impl) -> Apply impl a -> Apply spec a
    repr1f :: Type a -> (Proxy spec, Proxy impl) -> Apply spec a -> Apply impl a

{-
class GaloisConnection1F spec impl where
    abstr1f :: IsType a => Proxy a -> Apply impl a -> Apply spec a
    repr1f :: IsType a => Proxy a -> Apply spec a -> Apply impl a
-}

------------------------------------------------------------
-- Derived interpreters
------------------------------------------------------------

class (Semantics f, GaloisConnection1F f g) => DerivedSemantics f g where
    intLitD :: (Proxy f, Proxy g) -> Int -> Apply g Int
    intLitD pfg i =
        repr1f (typeRep :: Type Int) pfg $ intLit (Proxy :: Proxy f) i

    boolLitD :: (Proxy f, Proxy g) -> Bool -> Apply g Bool
    boolLitD (pf, pg) b =
        repr1f (typeRep :: Type Bool) (pf, pg) $ boolLit pf b

    lamD :: (Type a, Type b) -> (Proxy f, Proxy g) -> (Apply g a -> Apply g b) -> Apply g (a -> b)
    lamD (tpa :: Type a, tpb :: Type b) (pf, pg) (f :: Apply g a -> Apply g b) =
        repr1f (Arrow tpa tpb) (pf, pg) $ lam pf $ (abstr1f tpb (pf, pg)) . f . (repr1f tpa (pf, pg))

    appD :: (Proxy f, Proxy g) -> Apply g (a -> b) -> Apply g a -> Apply g b

    if_D :: (Proxy f, Proxy g) -> Apply g Bool -> Apply g a -> Apply g a -> Apply g a

    ltD :: (Proxy f, Proxy g) -> Apply g Int -> Apply g Int -> Apply g Bool
    plusD :: (Proxy f, Proxy g) -> Apply g Int -> Apply g Int -> Apply g Int

    retD :: (Proxy f, Proxy g) -> Apply g a -> Apply g (InterpM a)
    bindD :: (Proxy f, Proxy g) -> Apply g (InterpM a) -> Apply g (a -> InterpM b) -> Apply g (InterpM b)
    incrD :: (Proxy f, Proxy g) -> Apply g (InterpM Int)

------------------------------------------------------------
-- Relating the staged and unstaged interpreters
------------------------------------------------------------

bottom = bottom

idToTerm :: Type a -> a -> Term a
idToTerm Int i = IntLit i
idToTerm Bool b = BoolLit b
idToTerm (Arrow tp1 tp2) f =
    Lam $ nu $ \_ -> idToTerm tp2 $ f bottom
--idToTerm (M tp) m = interpMToTerm $ m >>= return . idToTerm tp
idToTerm (M tp) m = bottom

--interpMToTerm :: InterpM (Term a) -> Term (InterpM a)
--interpMToTerm m = Ret $ runIdentity $ (runStateT $ unInterpM m) bottom

instance GaloisConnection1F Id TermF where
    abstr1f _ = eval
    repr1f _ x = idToTerm typeRep x

-- FIXME: I don't think the above is a Galois connection!!!


------------------------------------------------------------
-- online partial evaluation
------------------------------------------------------------

newtype SInterpM f a = SInterpM { unSInterpM :: StateT (Apply f Int) Identity a }


{-
data PEF_static f
type instance Apply (PEF_static f) Int = Apply f Int
type instance Apply (PEF_static f) Bool = Apply f Bool
type instance Apply (PEF_static f) (a -> b) =
    (Apply (PEF_static f) a) -> (Apply (PEF_static f) b)
type instance Apply (PEF_static f) (InterpM a) =
    SInterpM f (Apply (PEF_static f) a)

data PEF f
type instance Apply (PEF f) a = (Maybe (Apply (PEF_static f) a), Apply f a)
-}

data PEF f
type instance Apply (PEF f) Int = (Maybe Int, Apply f Int)
type instance Apply (PEF f) Bool = (Maybe Bool, Apply f Bool)
type instance Apply (PEF f) (a -> b) =
    (Maybe (Apply (PEF f) a -> Apply (PEF f) b), Apply f (a -> b))
type instance Apply (PEF f) (InterpM a) =
    (Maybe (SInterpM f (Apply (PEF f) a)), Apply f (InterpM a))

instance GaloisConnection1F f (PEF f) where
    abstr1f (Proxy :: Proxy a) (x :: Apply (PEF f) a) =
        case typeRep :: Type a of
          Int -> snd x
          Bool -> snd x
          Arrow _ _ -> snd x
          M _ -> snd x
    repr1f (Proxy :: Proxy a) (x :: Apply f a) =
        case typeRep :: Type a of
          Int -> (Nothing, x)
          Bool -> (Nothing, x)
          Arrow _ _ -> (Nothing, x)
          M _ -> (Nothing, x)


{-
instance Semantics f => Semantics (PEF f) where
    intLit (Proxy :: Proxy (PEF f)) i = (Just i, intLit (Proxy :: Proxy f) i)
    boolLit (Proxy :: Proxy (PEF f)) b = (Just b, boolLit (Proxy :: Proxy f) b)

    lam (Proxy :: Proxy (PEF f)) (ff :: Apply (PEF f) a -> Apply (PEF f) b) =
        (Just ff, lam (Proxy :: Proxy f) (\x -> repr1f . ff . abstr1f))
-}
{-
    app = App

    if_ = If

    lt = Lt
    plus = Plus

    ret = Ret
    bind = Bind
    incr = Incr
-}
