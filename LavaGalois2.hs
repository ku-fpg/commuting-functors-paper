{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, OverlappingInstances #-}
{-# LANGUAGE DefaultSignatures #-}

module LavaGalois where

import Galois

import Data.Maybe (fromJust)
import Data.List (transpose)

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

zipWithS :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWithS f (Cons x xs) (Cons y ys) = Cons (f x y) $ zipWithS f xs ys

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

-- the high-level, abstract implementation as a Haskell term
instance LavaSemantics Stream where
    unconnected = fromList $ repeat False

    not1 = fmap Prelude.not
    and2 s1 s2 = zipWithS (&&) s1 s2
    xor2 s1 s2 = zipWithS (/=) s1 s2

-- ghci> halfAdder (fromList $ cycle [False,True]) (fromList $ cycle [False,False,True,True])

class Step1 a where
    type Step1T a
    unwrap :: Step1T a -> a
    wrap :: a -> Step1T a

instance (Functor f, Step1 a) => Step1 (f a) where
    type Step1T (f a) = f (Step1T a)
    unwrap = fmap unwrap
    wrap = fmap wrap

instance Step1 Bool where
    type Step1T Bool = Maybe Bool
    unwrap Nothing = False
    unwrap (Just b) = b
    wrap b = Just b

newtype Step1F a = Step1F { unStep1F :: Step1T (Stream a) }

instance Step1 a => GaloisConnection (Stream a) (Step1F a) where
    abstr = unwrap . unStep1F
    repr = Step1F . wrap

instance LavaSemantics Step1F where
    unconnected = Step1F $ fromList $ repeat Nothing

    not1 = repr (not1 :: Stream Bool -> Stream Bool)
    and2 = repr (and2 :: Stream Bool -> Stream Bool -> Stream Bool)
    xor2 = repr (xor2 :: Stream Bool -> Stream Bool -> Stream Bool)

evalStep1 = unStep1F

class Step2 a where
    type Step2T a
    uncommute :: Step2T a -> a
    commute :: a -> Step2T a

instance Step2 (Stream (Maybe a)) where
    type Step2T (Stream (Maybe a)) = Maybe (Stream a)
    uncommute Nothing = fromList $ repeat Nothing
    uncommute (Just s) = fmap Just s
    commute s@(Cons x _) = maybe Nothing (const $ Just $ fmap fromJust s) x

newtype Step2F a = Step2F { unStep2F :: Step2T (Step1T (Stream a)) }

instance (Step2 (Step1T (Stream a))) => GaloisConnection (Step1F a) (Step2F a) where
    abstr = Step1F . uncommute . unStep2F
    repr = Step2F . commute . unStep1F

instance LavaSemantics Step2F where
    unconnected = repr (unconnected :: Step1F Bool)

    not1 = repr (not1 :: Step1F Bool -> Step1F Bool)
    and2 = repr (and2 :: Step1F Bool -> Step1F Bool -> Step1F Bool)
    xor2 = repr (xor2 :: Step1F Bool -> Step1F Bool -> Step1F Bool)

evalStep2 = unStep2F

------------------------------------------------------------
-- Box function from the paper.
------------------------------------------------------------

box :: Bool -> [Stream Bool] -> Stream Bool
box init nss = res
  where res = Cons init $ zipWithS step (transposeLS nss) res

        -- we played fast and loose with 'transpose' in the paper
        transposeLS :: [Stream Bool] -> Stream [Bool]
        transposeLS = fromList . transpose . fmap toList

step :: [Bool] -> Bool -> Bool
step ns live | live && neighbors == 2 = True
             | live && neighbors == 3 = True
             | not live && neighbors == 3 = True
             | otherwise = False
  where neighbors = length (filter id ns)
