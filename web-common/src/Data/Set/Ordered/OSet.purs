module Data.Set.Ordered.OSet (OSet, fromFoldable, filter, insert) where

import Prelude
import Data.Array as Array
import Data.Foldable (class Foldable)

newtype OSet a
  = OSet (Array a)

instance semigroupOSet :: Ord a => Semigroup (OSet a) where
  append = appendOSet

instance monoidOSet :: Ord a => Monoid (OSet a) where
  mempty = OSet mempty

instance foldableOSet :: Foldable OSet where
  foldr f acc (OSet s) = Array.foldr f acc s
  foldl f acc (OSet s) = Array.foldl f acc s
  foldMap f (OSet s) = Array.foldMap f s

fromFoldable :: forall f a. Ord a => Foldable f => f a -> OSet a
fromFoldable = OSet <<< Array.nub <<< Array.fromFoldable

appendOSet :: forall a. Ord a => OSet a -> OSet a -> OSet a
appendOSet (OSet om1) (OSet om2) = OSet (Array.nub (om1 <> om2))

filter :: forall a. (a -> Boolean) -> OSet a -> OSet a
filter f (OSet os) = OSet $ Array.filter f os

singleton :: forall a. Ord a => a -> OSet a
singleton x = OSet (Array.singleton x)

insert :: forall a. Ord a => a -> OSet a -> OSet a
insert a os = os <> singleton a
