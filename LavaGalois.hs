{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, OverlappingInstances #-}
{-# LANGUAGE DefaultSignatures #-}

module LavaGalois where

import Galois

--import Data.Proxy


------------------------------------------------------------
-- FProxy objects
------------------------------------------------------------

data FProxy (f :: * -> *) = FProxy


------------------------------------------------------------
-- Streams
------------------------------------------------------------

data Stream a = Cons !a (Stream a)

instance Functor Stream where
    fmap f (Cons x s) = Cons (f x) (fmap f s)

instance Show a => Show (Stream a) where
    show = show . take 20 . toList

toList :: Stream a -> [a]
toList (Cons x s) = x : toList s

fromList :: [a] -> Stream a
fromList (x:xs) = Cons x $ fromList xs
fromList [] = error "fromList: empty list!"


------------------------------------------------------------
-- Lava Semantics
------------------------------------------------------------

-- I hate writing "Identity" all the time...
newtype Id a = Id { unId :: a }

instance Functor Id where
    fmap f = Id . f . unId

-- the top-level definition
class LavaSemantics f where
    unconnected :: f (Stream Bool)

    not1 :: f (Stream Bool) -> f (Stream Bool)
    and2 :: f (Stream Bool) -> f (Stream Bool) -> f (Stream Bool)
    xor2 :: f (Stream Bool) -> f (Stream Bool) -> f (Stream Bool)

    -- default for all methods uses a GaloisConnection to Id
   {-
    default unconnected :: (GaloisConnection1 g f, LavaSemantics g) => f (Stream Bool)
    unconnected = repr (unconnected :: g (Stream Bool))
    default not1 :: GaloisConnection1 Id f => f (Stream Bool) -> f (Stream Bool)
    not1 = repr (not1 :: Id (Stream Bool) -> Id (Stream Bool))
    default and2 :: GaloisConnection1 Id f => f (Stream Bool) -> f (Stream Bool) -> f (Stream Bool)
    and2 = repr (and2 :: Id (Stream Bool) -> Id (Stream Bool) -> Id (Stream Bool))
    default xor2 :: GaloisConnection1 Id f => f (Stream Bool) -> f (Stream Bool) -> f (Stream Bool)
    xor2 = repr (xor2 :: Id (Stream Bool) -> Id (Stream Bool) -> Id (Stream Bool))
    -}


-- the high-level, abstract implementation as a Haskell term
instance LavaSemantics Id where
    unconnected = Id $ fromList $ repeat False

    not1 = Id . (fmap Prelude.not) . unId
    and2 s1 s2 = (Id $ fromList $
                  zipWith (&&) (toList (unId s1)) (toList (unId s2)))
    xor2 s1 s2 = (Id $ fromList $
                  zipWith (/=) (toList (unId s1)) (toList (unId s2)))


-- to make it easy to build implementations piecewise
{-
class (GaloisConnection1 f g, LavaSemantics f) => DerivedLavaSemantics f g | g -> f where
    unconnectedD :: g (Stream Bool)
    unconnectedD = repr (unconnected :: f (Stream Bool))

    not1D :: g (Stream Bool) -> g (Stream Bool)
    not1D = repr (not1 :: f (Stream Bool) -> f (Stream Bool))
    and2D :: g (Stream Bool) -> g (Stream Bool) -> g (Stream Bool)
    and2D = repr (and2 :: f (Stream Bool) -> f (Stream Bool) -> f (Stream Bool))
    xor2D :: g (Stream Bool) -> g (Stream Bool) -> g (Stream Bool)
    xor2D = repr (xor2 :: f (Stream Bool) -> f (Stream Bool) -> f (Stream Bool))

-- NOTE: this causes undecidable instances in general...
instance DerivedLavaSemantics f g => LavaSemantics g where
    unconnected = unconnectedD
    not1 = not1D
    and2 = and2D
    xor2 = xor2D
-}

------------------------------------------------------------
-- Step 1 of Refinement of Lava Semantics
------------------------------------------------------------

class Impl1 a where
    type Impl1Type a
    abstrI1 :: Impl1Type a -> a
    reprI1 :: a -> Impl1Type a

instance Impl1 Bool where
    type Impl1Type Bool = Maybe Bool
    abstrI1 Nothing = False
    abstrI1 (Just b) = b
    reprI1 b = Just b

instance (Functor f, Impl1 a) => Impl1 (f a) where
    type Impl1Type (f a) = f (Impl1Type a)
    abstrI1 = fmap abstrI1
    reprI1 = fmap reprI1

newtype Impl1TypeF a = Impl1TypeF { unImpl1TypeF :: Impl1Type a }

instance Impl1 a => GaloisConnection (Id a) (Impl1TypeF a) where
    abstr = Id . abstrI1 . unImpl1TypeF
    repr = Impl1TypeF . reprI1 . unId

instance LavaSemantics Impl1TypeF where
    unconnected = Impl1TypeF $ fromList $ repeat Nothing

    not1 = repr (not1 :: Id (Stream Bool) -> Id (Stream Bool))
    and2 = repr (and2 :: Id (Stream Bool) -> Id (Stream Bool) -> Id (Stream Bool))
    xor2 = repr (xor2 :: Id (Stream Bool) -> Id (Stream Bool) -> Id (Stream Bool))
