module Marlowe.Extended.OrderedSet (OrderedSet, fromFoldable, filter, insert) where

import Prelude
import Data.Array as Array
import Data.Foldable (class Foldable)

newtype OrderedSet a
  = OrderedSet (Array a)

instance semigroupOrderedSet :: Ord a => Semigroup (OrderedSet a) where
  append = appendOrderedSet

instance monoidOrderedSet :: Ord a => Monoid (OrderedSet a) where
  mempty = OrderedSet mempty

instance foldableOrderedSet :: Foldable OrderedSet where
  foldr f acc (OrderedSet s) = Array.foldr f acc s
  foldl f acc (OrderedSet s) = Array.foldl f acc s
  foldMap f (OrderedSet s) = Array.foldMap f s

fromFoldable :: forall f a. Ord a => Foldable f => f a -> OrderedSet a
fromFoldable = OrderedSet <<< Array.nub <<< Array.fromFoldable

appendOrderedSet :: forall a. Ord a => OrderedSet a -> OrderedSet a -> OrderedSet a
appendOrderedSet (OrderedSet om1) (OrderedSet om2) = OrderedSet (Array.nub (om1 <> om2))

filter :: forall a. (a -> Boolean) -> OrderedSet a -> OrderedSet a
filter f (OrderedSet os) = OrderedSet $ Array.filter f os

singleton :: forall a. Ord a => a -> OrderedSet a
singleton x = OrderedSet (Array.singleton x)

insert :: forall a. Ord a => a -> OrderedSet a -> OrderedSet a
insert a os = os <> singleton a
