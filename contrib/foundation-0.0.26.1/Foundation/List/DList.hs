-- |
-- Module      : Foundation.List.DList
-- License     : BSD-style
-- Maintainer  : Nicolas Di Prima <nicolas@primetype.co.uk>
-- Stability   : statble
-- Portability : portable
--
-- Data structure for optimised operations (append, cons, snoc) on list
--
module Foundation.List.DList
    ( DList
    ) where

import Basement.Compat.Base
import Basement.Compat.Semigroup
import Basement.Compat.Bifunctor
import Foundation.Collection

newtype DList a = DList { unDList :: [a] -> [a] }
  deriving (Typeable)

instance Eq a => Eq (DList a) where
    (==) dl1 dl2 = (==) (toList dl1) (toList dl2)

instance Ord a => Ord (DList a) where
    compare dl1 dl2 = compare (toList dl1) (toList dl2)

instance Show a => Show (DList a) where
    show = show . toList

instance IsList (DList a) where
    type Item (DList a) = a
    fromList = DList . (Basement.Compat.Semigroup.<>)
    toList = flip unDList []

instance Semigroup (DList a) where
    (<>) dl1 dl2 = DList $ unDList dl1 . unDList dl2
instance Monoid (DList a) where
    mempty = DList id
    mappend dl1 dl2 = DList $ unDList dl1 . unDList dl2

instance Functor DList where
    fmap f = foldr (cons . f) mempty

instance Applicative DList where
    pure = singleton
    (<*>) m1 m2 = m1 >>= \x1 -> m2 >>= \x2 -> return (x1 x2)

instance Monad DList where
    (>>=) m k = foldr (mappend . k) mempty m
    return = singleton

type instance Element (DList a) = a

instance Foldable (DList a) where
    foldr f b = foldr f b . toList
    foldl' f b = foldl' f b . toList

instance Collection (DList a) where
    null = null . toList
    length = length . toList
    elem a = elem a . toList
    maximum = maximum . nonEmpty_ . toList
    minimum = minimum . nonEmpty_ . toList
    all f = all f . toList
    any f = any f . toList

instance Sequential (DList a) where
    take n = fromList . take n . toList
    revTake n = fromList . revTake n . toList
    drop n = fromList . drop n . toList
    revDrop n = fromList . revDrop n . toList
    splitAt n = bimap fromList fromList . splitAt n . toList
    splitOn f = fmap fromList . splitOn f . toList
    break f = bimap fromList fromList . break f . toList
    breakEnd f = bimap fromList fromList . breakEnd f . toList
    breakElem e = bimap fromList fromList . breakElem e . toList
    intersperse e = fromList . intersperse e . toList
    intercalate e = intercalate e . toList
    span f = bimap fromList fromList . span f . toList
    spanEnd f = bimap fromList fromList . spanEnd f . toList
    filter f = fromList . filter f . toList
    partition f = bimap fromList fromList . partition f . toList
    reverse = fromList . reverse . toList
    uncons dl = second fromList <$> uncons (toList dl)
    unsnoc dl = first fromList <$> unsnoc (toList dl)
    cons e dl = DList $ (:) e . unDList dl
    snoc dl e = DList $ unDList dl . (:) e
    find f = find f . toList
    sortBy comp = fromList . sortBy comp . toList
    singleton = DList . (:)
    replicate n e = fromList $ replicate n e
