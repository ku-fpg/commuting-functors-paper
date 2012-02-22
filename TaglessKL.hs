{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables #-}

-- Syntax of a crude approximation of KL
class Lava repr where
    -- Base types: what we currently use Rep and Type for
    bool :: Bool -> repr Bool

    -- Primitives: no idea what should go here
    not  :: repr Bool -> repr Bool
    and2 :: repr Bool -> repr Bool -> repr Bool
    xor2 :: repr Bool -> repr Bool -> repr Bool

    -- BitWidth constraints so we can compile.
    pack :: (BitWidth a, BitWidth b) => repr a -> repr b -> repr (a,b)
    unpack :: (BitWidth a, BitWidth b) => repr (a,b) -> (repr a, repr b)

-- Our test circuits, defined in terms of syntax above.
-- halfAdder :: (Lava repr) => repr Bool -> repr Bool -> repr (Bool, Bool)
halfAdder a b = pack carry sum
    where carry = and2 a b
          sum   = xor2 a b

-- Infered type:
-- fullAdder :: (Lava repr) => repr Bool -> repr Bool -> repr Bool -> repr (Bool, Bool)
fullAdder a b cin = pack cout sum
    where (c1,s1)  = unpack $ halfAdder a b
          (c2,sum) = unpack $ halfAdder cin s1
          cout     = xor2 c1 c2

-- Semantics #1: Combinatorial Circuit
-- As they point out in the Finally Tagless paper, C is not a tag.
newtype Comb a = C { unC :: a }

instance Show a => Show (Comb a) where
    show = show . unC

instance Lava Comb where
    bool = C

    not      = C . Prelude.not . unC
    and2 a b = C $ (unC a) && (unC b)
    xor2 a b = C $ (unC a) /= (unC b)

    pack a b = C (unC a, unC b)
    unpack a = (C $ fst t, C $ snd t)
        where t = unC a

evalComb = unC
-- evalComb $ halfAdder (bool True) (bool False)
-- evalComb $ fullAdder (bool True) (bool True) (bool True)

-- Digression: Streams
data Stream a = Cons !a (Stream a)

instance Functor Stream where
    fmap f (Cons x s) = Cons (f x) (fmap f s)

instance Show a => Show (Stream a) where
    show = show . take 20 . toList

toList :: Stream a -> [a]
toList (Cons x s) = x : toList s

fromList :: [a] -> Stream a
fromList (x:xs) = Cons x $ fromList xs
fromList []     = error "fromList: empty list!"
-- End Digression

-- Semantics #2: Sequential, dataflow-style circuits.
newtype Seq a = S { unS :: Stream a }

instance Show a => Show (Seq a) where
    show = show . unS

instance Lava Seq where
    bool = S . fromList . repeat

    not = S . fmap Prelude.not . unS
    and2 s1 s2 = S $ fromList $ zipWith (&&) (toList (unS s1)) (toList (unS s2))
    xor2 s1 s2 = S $ fromList $ zipWith (/=) (toList (unS s1)) (toList (unS s2))

    pack s1 s2 = S $ fromList $ zip          (toList (unS s1)) (toList (unS s2))
    unpack s = (S $ fromList s1, S $ fromList s2)
        where (s1,s2) = unzip $ toList $ unS s

toSeq :: [a] -> Seq a
toSeq = S . fromList

evalSeq = unS
-- evalSeq $ fullAdder (toSeq $ cycle [True,False]) (toSeq $ cycle [True,True,False,False]) (toSeq $ cycle [False,False,True])

-- Digression: Wire Width
type Width = Int

-- Invariant to maintain: width DOES NOT evaluate its argument
class Show a => BitWidth a where
    width :: a -> Width

instance BitWidth Bool where width _ = 1

instance (BitWidth a, BitWidth b) => BitWidth (a,b) where
    width _ = width (undefined :: a) + width (undefined :: b)
-- End Digression

-- Semantics #3: Entity graph, for VHDL generation.
data Driver = forall a. Show a => D (Entity a)

instance Show Driver where
    show (D e) = show e

--                name   output          inputs
data Entity a = E String (String, Width) [(String, Width, Driver)]
    deriving (Show)

instance BitWidth a => BitWidth (Entity a) where
    width _ = width (undefined :: a)

instance Lava Entity where
    bool True  = E "constTrue"  ("o0", 1) []
    bool False = E "constFalse" ("o0", 1) []

    not e      = E "primNot" ("o0", 1) [("i0", 1, D e)]
    and2 e1 e2 = E "primAnd" ("o0", 1) [("i0", 1, D e1), ("i1", 1, D e2)]
    xor2 e1 e2 = E "primXor" ("o0", 1) [("i0", 1, D e1), ("i1", 1, D e2)]

    pack e1 e2 = E "primPack" ("o0", x + y) [("i0", x, D e1), ("i1", y, D e2)]
        where x = width e1
              y = width e2

    unpack e   = (e1, e2)
        where e1 = E "primFst" ("o0", width e1) [("i0", w, D e)]
              e2 = E "primSnd" ("o0", width e2) [("i0", w, D e)]
              w  = width e

compile :: Entity a -> String
compile = {- todo: recover sharing -} show
