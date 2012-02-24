{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, OverlappingInstances #-}
{-# LANGUAGE DefaultSignatures #-}

module LavaGalois where

import Galois

import Data.Maybe (fromJust)

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

-- the top-level definition
class LavaSemantics f where
    unconnected :: f Bool

    not1 :: f Bool -> f Bool
    and2 :: f Bool -> f Bool -> f Bool
    xor2 :: f Bool -> f Bool -> f Bool

-- Inferred type:
-- halfAdder :: LavaSemantics f => f Bool -> f Bool -> (f Bool, f Bool)
halfAdder x y = (carry, sum)
    where carry = and2 x y
          sum   = xor2 x y

{-
-- I originally implemented the semantics for Id, then
-- transformed to work over Streams with Wrap (below).
-- This 'worked' (in that a working function was derived),
-- but the streams couldn't vary. This makes sense given
-- our options for unwrap/wrap below, but maybe it means
-- my Wrap class isn't very useful.
newtype Id a = Id a deriving (Show)
unId (Id x) = x

instance Functor Id where
    fmap f = Id . f . unId

instance LavaSemantics Id where
    unconnected = Id False

    not1 = fmap Prelude.not
    and2 (Id x) (Id y) = Id $ x && y
    xor2 (Id x) (Id y) = Id $ x /= y

instance Wrap Stream Bool where
    data WrapT Stream Bool = WSB { unWSB :: Stream Bool }
    unwrap (WSB (Cons b _)) = b
    wrap b = WSB s where s = Cons b s

instance LavaSemantics (WrapF Id Stream) where
    unconnected = repr (unconnected :: Id Bool)

    not1 = repr (not1 :: Id Bool -> Id Bool)
    and2 = repr (and2 :: Id Bool -> Id Bool -> Id Bool)
    xor2 = repr (xor2 :: Id Bool -> Id Bool -> Id Bool)
-}

-- the high-level, abstract implementation as a Haskell term
instance LavaSemantics Stream where
    unconnected = fromList $ repeat False

    not1 = fmap Prelude.not
    and2 s1 s2 = zipWithS (&&) s1 s2
    xor2 s1 s2 = zipWithS (/=) s1 s2

-- ghci> halfAdder (fromList $ cycle [False,True]) (fromList $ cycle [False,False,True,True])

------------------------------------------------------------
-- Ability to wrap a value in a functor, in a given context.
------------------------------------------------------------

-- Unfortunately, we need injectivity, so must use a data
-- family instead of a type family. This is mostly an issue
-- when supplying input to our derived function, as the
-- constructors must be in the right places.
class Wrap (f :: * -> *) a where
    data WrapT f a
    unwrap :: WrapT f a -> a
    wrap   :: a -> WrapT f a

instance (Functor g, Wrap f a) => Wrap f (g a) where
    data WrapT f (g a) = WF { unWF :: g (WrapT f a) }
    unwrap (WF gfa) = fmap unwrap gfa
    wrap = WF . fmap wrap

newtype WrapF c f a = WrapF { unWrapF :: WrapT f (c a) }

-- Requires UndecidableInstances... we can just manually unpack
-- things and show them ourselves.
-- instance Show (WrapT a) => Show (WrapF a) where
--     show = show . unWrapF

-- Does this make sense? It certainly works in that it typechecks
-- and gives working derived functions, but I obviously don't
-- have many testcases.
instance (Functor c, Wrap f (c a)) => GaloisConnection (c a) (WrapF c f a) where
    abstr = unwrap . unWrapF
    repr = WrapF . wrap

------------------------------------------------------------
-- Step 1: Stream Bool ==> Stream (Maybe Bool)
------------------------------------------------------------

instance Wrap Maybe Bool where
    data WrapT Maybe Bool = WMB { unWMB :: Maybe Bool }
    unwrap (WMB Nothing) = False
    unwrap (WMB (Just b)) = b
    wrap = WMB . Just

instance LavaSemantics (WrapF Stream Maybe) where
    unconnected = repr (unconnected :: Stream Bool)

    not1 = repr (not1 :: Stream Bool -> Stream Bool)
    and2 = repr (and2 :: Stream Bool -> Stream Bool -> Stream Bool)
    xor2 = repr (xor2 :: Stream Bool -> Stream Bool -> Stream Bool)

-- This works...
-- ghci> let r = unconnected :: WrapF Stream Maybe Bool
-- ghci> fmap unWMB $ unWF $ unWrapF r
-- ghci> let r2 = not1 (WrapF $ WF $ fmap (WMB . Just) $ fromList $ cycle [True,False,False])
-- ghci> fmap unWMB $ unWF $ unWrapF r2
-- ghci> let r3 = and2 (WrapF $ WF $ fmap (WMB . Just) $ fromList $ cycle [True,False]) (WrapF $ WF $ fmap (WMB . Just) $ fromList $ cycle [True,True,False,False])
-- ghci> fmap unWMB $ unWF $ unWrapF r3

------------------------------------------------------------
-- Step 2: Stream (Maybe Bool) -> Maybe (Stream Bool)
------------------------------------------------------------
{-

class Impl2 f g where
    type Impl2Type f g a
    abstrI2 :: Impl2Type f g a -> f (g a)
    reprI2 :: f (g a) -> Impl2Type f g a

instance Impl2 Stream Maybe where
    type Impl2Type Stream Maybe a = Maybe (Stream a)
    abstrI2 Nothing = fromList $ repeat Nothing
    abstrI2 (Just s) = fmap Just s
    reprI2 s@(Cons x _) = maybe Nothing (const $ Just $ fmap fromJust s) x

instance (Functor h, Impl2 f g) => Impl2 (h :. f) g where
    type Impl2Type (h :. f) g a = h (Impl2Type f g a)
    abstrI2 = C . fmap abstrI2
    reprI2 = fmap reprI2 . unC

newtype Impl2TypeF f g a = Impl2TypeF { unImpl2TypeF :: Impl2Type f g a }

newtype (f :. g) a = C { unC :: f (g a) }

-- ugh at the type equality
instance (Impl1Type a ~ g a, Impl2 f g) => GaloisConnection (Impl1TypeF (f a)) (Impl2TypeF f g a) where
    abstr = Impl1TypeF . abstrI2 . unImpl2TypeF
    repr = Impl2TypeF . reprI2 . unImpl1TypeF

instance LavaSemantics (Impl2TypeF Stream Maybe) where
    unconnected = Impl2TypeF Nothing

    not1 = repr (not1 :: Impl1TypeF (Stream Bool) -> Impl1TypeF (Stream Bool))
--    and2 = repr (and2 :: Impl1TypeF (Stream Bool) -> Impl1TypeF (Stream Bool) -> Impl1TypeF (Stream Bool))
--    xor2 = repr (xor2 :: Impl1TypeF (Stream Bool) -> Impl1TypeF (Stream Bool) -> Impl1TypeF (Stream Bool))

{-
class Impl2 f g where
    data Impl2Type f g a -- we need injectivity
    abstrI2 :: Impl2Type f g a -> f (g a)
    reprI2 :: f (g a) -> Impl2Type f g a

instance Impl2 Stream Maybe where
    data Impl2Type Stream Maybe a = I2SM (Maybe (Stream a))
    abstrI2 (I2SM Nothing) = fromList $ repeat Nothing
    abstrI2 (I2SM (Just s)) = fmap Just s
    reprI2 s@(Cons x _) = I2SM $ maybe Nothing (const $ Just $ fmap fromJust s) x

instance (Functor h, Impl2 f g) => Impl2 (h :. f) g where
    data Impl2Type (h :. f) g a = I2F (h (Impl2Type f g a))
    abstrI2 (I2F hfg) = C $ fmap abstrI2 hfg
    reprI2 = I2F . fmap reprI2 . unC
-}
-}
