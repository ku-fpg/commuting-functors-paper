{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}

module Galois where


------------------------------------------------------------
-- Galois Connections
------------------------------------------------------------

-- base class
class GaloisConnection spec impl where
    abstr :: impl -> spec
    repr :: spec -> impl
    {- proof obligations:
       (<i) :: Relation impl impl
       (<s) :: Relation spec spec
       forall (s:spec) (i:impl) , abstr i <s s <=> i <i repr s
    -} 

-- versions for functors
class GaloisConnection1 spec impl where
    abstr1 :: GaloisConnection spec1 impl1 => impl impl1 -> spec spec1
    repr1 :: GaloisConnection spec1 impl1 => spec spec1 -> impl impl1

class GaloisConnection2 spec impl where
    abstr2 :: (GaloisConnection spec1 impl1, GaloisConnection spec2 impl2) =>
              impl impl1 impl2 -> spec spec1 spec2
    repr2 :: (GaloisConnection spec1 impl1, GaloisConnection spec2 impl2) =>
             spec spec1 spec2 -> impl impl1 impl2

-- versions to derive instances from instances for functors
instance (GaloisConnection1 f g, GaloisConnection a b) =>
    GaloisConnection (f a) (g b) where
        abstr = abstr1
        repr = repr1

instance (GaloisConnection2 spec impl, GaloisConnection spec1 impl1) =>
    GaloisConnection1 (spec spec1) (impl impl1) where
        abstr1 = abstr2
        repr1 = repr2

-- actual, real instances
instance GaloisConnection a a where
        abstr = id
        repr = id

instance GaloisConnection2 (->) (->) where
        abstr2 f = abstr . f . repr
        repr2 f = repr . f . abstr

instance Functor f => GaloisConnection1 f f where
        abstr1 = fmap abstr
        repr1 = fmap repr

{-
instance GaloisConnection1 [] [] where
        abstr1 = map abstr
        repr1 = map repr

instance GaloisConnection1 Stream Stream where
        abstr1 = fmap abstr
        repr1 = fmap repr
-}
