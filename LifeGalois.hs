{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, OverlappingInstances #-}
{-# LANGUAGE DefaultSignatures #-}

module LavaGalois where

import Galois

import Data.Maybe (fromJust)
import Data.List (transpose)

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

zipWithS :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWithS f (Cons x xs) (Cons y ys) = Cons (f x y) $ zipWithS f xs ys

------------------------------------------------------------
-- Box function from the paper.
------------------------------------------------------------

-- life box is dim^2 spaces
dim = 5

-- I bet we need a ListSemantics
class LifeSemantics lst f where
    -- todo: can we move these 3 into life?
    unconnected :: FProxy lst -> f Bool

    box :: FProxy lst -> Bool -> lst (f Bool) -> f Bool

    -- NB: using [] here, because we are not looking
    -- to transform this particular list
--    neighbors :: [f Bool] -> [lst (f Bool)] -- [Stream Bool] -> [[Stream Bool]] => [Maybe (Stream Bool)] -> [Tuple8 (Maybe (Stream Bool))]

    transposeLF :: lst (f Bool) -> f (lst Bool)

    -- first argument is like an implicit argument in agda
    -- we need the lst implmentation for box
    life :: FProxy lst -> [Bool] -> [f Bool]

instance LifeSemantics [] Stream where
    unconnected _proxy = fromList $ repeat False

    box _proxy init nss = res
        where res = Cons init $ zipWithS step (transposeLF nss) res
              step ns live | live && neighbors == 2 = True
                           | live && neighbors == 3 = True
                           | not live && neighbors == 3 = True
                           | otherwise = False
                where neighbors = length (filter id ns)

    life proxy inits | length inits == dim * dim = res
               | otherwise = error $ "initial board should be " ++ show (dim * dim) ++ " squares"
        where res = zipWith (box proxy) inits neighbors
              neighbors = [ map neighbor [i-dim-1, i-dim, i-dim+1, i-1, i+1, i+dim-1, i+dim, i+dim+1]
                          | i <- [1..dim*dim] ]
              -- neighbor :: Int -> f Bool
              neighbor n | n >= 1 && n <= dim*dim = res !! (n-1)
                         | otherwise = unconnected proxy

    transposeLF = transposeLS

-- box_impl :: Bool -> Tuple8 (Maybe (Signal Bool)) -> Signal Bool

listProxy :: FProxy []
listProxy = FProxy

transposeLS :: [Stream a] -> Stream [a]
transposeLS = fromList . transpose . fmap toList

pp :: [Stream Bool] -> IO ()
pp = mapM_ pr . take 20 . toList . transposeLS
    where pr board | or board = mapM_ putStrLn
                              $ chunk
                              $ map (\x -> if x then 'X' else '_') board
                   | otherwise = return ()
          chunk [] = [""]
          chunk l = take dim l : chunk (drop dim l)

-- Example on page 1 of the paper:
-- NB: type ascription necessary because composition of pp and life
-- leaves f underspecified just like show . read
--
-- pp (life listProxy $ replicate 8 False ++ [True,False,False,True,False,True,False,False,False,True,True] ++ replicate 6 False :: [Stream Bool])

------------------------------------------------------------
-- Step 1: Stream a ==> Stream (Maybe a)
------------------------------------------------------------

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

instance LifeSemantics [] Step1F where
    unconnected _ = Step1F $ fromList $ repeat Nothing

--  We have some problems with box and life, due to the FProxy and Bool arguments
--     box = repr (box :: FProxy [] -> Bool -> [Stream Bool] -> Stream Bool)
    transposeLF = repr (transposeLF :: [Stream Bool] -> Stream [Bool])
--    life = repr (life :: FProxy [] -> [Bool] -> [Stream Bool])

evalStep1 = unStep1F
-- ghci> evalStep1 (unconnected listProxy :: Step1F Bool)
-- ghci> evalStep1 $ transposeLF [Step1F $ fromList $ map Just $ cycle [True,False,False], Step1F $ fromList $ map Just $ cycle [True,False]]

------------------------------------------------------------
-- Step 3: [a] -> Tuple8 a
------------------------------------------------------------

class Step3 a where
    type Step3T a
    untuple :: Step3T a -> a
    tuple :: a -> Step3T a

{-
instance (Functor f, Step3 a) => Step3 (f a) where
    type Step3T (f a) = f (Step3T a)
    untuple = fmap untuple
    tuple = fmap tuple
-}

step3Proxy :: FProxy Step3F
step3Proxy = FProxy

instance Step3 [a] where
    type Step3T [a] = (a,a,a,a,a,a,a,a)
    untuple (a,b,c,d,e,f,g,h) = [a,b,c,d,e,f,g,h]
    tuple [a,b,c,d,e,f,g,h] = (a,b,c,d,e,f,g,h)
    tuple _                 = error "tuple: ill-formed list"

newtype Step3F a = Step3F { unStep3F :: Step3T [a] }

instance Step3 a => GaloisConnection [a] (Step3F a) where
    abstr = untuple . unStep3F
    repr = Step3F . tuple

instance LifeSemantics Step3F Step1F where
--    unconnected p = repr (unconnected :: FProxy [] -> Step1F Bool)

--  We have some problems with box and life, due to the FProxy and Bool arguments
--     box = repr (box :: FProxy [] -> Bool -> [Stream Bool] -> Stream Bool)
--     transposeLF = repr (transposeLF :: [Step1F Bool] -> Step1F [Bool])
--    life = repr (life :: FProxy [] -> [Bool] -> [Stream Bool])

evalStep3 = unStep3F
-- ghci> evalStep1 (unconnected listProxy :: Step1F Bool)
-- ghci> evalStep1 $ transposeLF [Step1F $ fromList $ map Just $ cycle [True,False,False], Step1F $ fromList $ map Just $ cycle [True,False]]
{-
------------------------------------------------------------
-- Step 2: Stream (Maybe a) ==> Maybe (Stream a)
------------------------------------------------------------

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
-}
