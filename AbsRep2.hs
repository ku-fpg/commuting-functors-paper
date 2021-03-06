{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, KindSignatures, FlexibleInstances,
             TypeOperators, TypeFamilies, LiberalTypeSynonyms, RankNTypes, FunctionalDependencies #-}

-- C is mnemonic for 'compose'
newtype (f :.: g) a = C { unC :: f (g a) }

instance (Show (f (g a))) => Show ((:.:) f g a) where
    show = show . unC

-- What I'd really like to have is a type synonym,
-- since it lacks a constructor:
--
-- type (f :.: g) a = f (g a)
--
-- But, even with LiberalTypeSynonyms,
-- you can't partially apply this in the instance header
-- below. GHC bug/feature request perhaps?
--
-- Using the newtype above means I have to fmap unC in
-- several places, and put the C back, which muddies
-- the code considerably.

-- c = context functor
-- f = abstract type
-- g = representation type
--
-- I'm not entirely sure we want the functional dependency here,
-- but it saves us ascribing a result type every time we call
-- rep and abs.
class WW c f a where
    type Rep c f a
    rep :: c (f a) -> Rep c f a
    abs :: Rep c f a -> c (f a)

newtype Id a = Id a  deriving (Show)
unId (Id x) = x

-- First something easy: commuting Maybe and Id
instance WW [] (Id :.: Maybe) a where
    type Rep [] (Id :.: Maybe) a = [(Maybe :.: Id) a]
    -- rep [Id (Maybe a)] -> [Maybe (Id a)]
    rep = fmap C . fmap (\(Id m) -> maybe Nothing (Just . Id) m) . fmap unC
    -- abs [Maybe (Id a)] -> [Id (Maybe a)]
    abs = fmap C . fmap (maybe (Id Nothing) (Id . Just . unId)) . fmap unC

-- Try in ghci:
-- rep $ fmap (C . Id) $ [Nothing,Nothing] ++ fmap Just [1..10]
-- Main.abs it

instance WW ([] :.: Maybe) Id a where
    type Rep ([] :.: Maybe) Id a = ([] :.: Maybe) a
    -- rep :: [Maybe (Id a)] -> [Maybe a]
    rep = C . fmap (fmap unId) . unC
    -- abs :: [Maybe a] -> [Maybe (Id a)]
    abs = C . fmap (fmap Id) . unC

-- This would really be quite elegant without the unC/C crap.
remId :: [(Id :.: Maybe) a] -> [Maybe a]
remId = unC . rep . C . fmap unC . rep
