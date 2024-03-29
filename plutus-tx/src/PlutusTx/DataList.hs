{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedLists    #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataList where

import PlutusTx.AsData qualified as AsData
import PlutusTx.DataPair (DataElem)
import PlutusTx.Foldable qualified as Foldable
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude hiding (all, any, elem, filter, foldr)
import Prelude qualified as H

AsData.asData
  [d|
    data List a = Nil | Cons a (List a)
      deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)
  |]

instance (DataElem a) => Semigroup (List a) where
  Nil <> l         = l
  (Cons x xs) <> l = Cons x (xs <> l)

instance (DataElem a) => Monoid (List a) where
  mempty = Nil

fromList :: DataElem a => [a] -> List a
fromList = Foldable.foldr Cons Nil

foldr :: DataElem a => (a -> b -> b) -> b -> List a -> b
foldr _ u Nil         = u
foldr f u (Cons x xs) = f x (foldr f u xs)

toList :: DataElem a => List a -> [a]
toList = foldr (:) []

map :: (DataElem a, DataElem b) => (a -> b) -> List a -> List b
map f = foldr (\a b -> Cons (f a) b) Nil

all :: DataElem a => (a -> Bool) -> List a -> Bool
all _ Nil         = True
all p (Cons x xs) = p x && all p xs

any :: DataElem a => (a -> Bool) -> List a -> Bool
any _ Nil         = False
any p (Cons x xs) = p x || any p xs

revAppend :: forall a. DataElem a => List a -> List a -> List a
revAppend = rev where
    rev :: List a -> List a -> List a
    rev Nil a         = a
    rev (Cons x xs) a = rev xs (Cons x a)

null :: List a -> Bool
null Nil = True
null _   = False

foldMap :: (DataElem a, Monoid m) => (a -> m) -> List a -> m
foldMap f = foldr (\a b -> f a <> b) mempty

fromSOP :: (DataElem a) => [a] -> List a
fromSOP = Foldable.foldr Cons Nil

elem :: (DataElem a, Eq a) => a -> List a -> Bool
elem _ Nil = False
elem a (Cons x xs)
  | a == x = True
  | otherwise = elem a xs

filter :: (DataElem a) => (a -> Bool) -> List a -> List a
filter _ Nil = Nil
filter p (Cons x xs)
  | p x = Cons x (filter p xs)
  | otherwise = filter p xs
