module Marlowe.Extended.OrderedMap (OrderedMap, alter, delete, fromFoldable, fromFoldableWithIndex, insert, isEmpty, keys, lookup, singleton, toUnfoldable, unionWith) where

import Prelude
import Data.Array as Array
import Data.Bifunctor (rmap)
import Data.Foldable (class Foldable, foldMap)
import Data.FoldableWithIndex (class FoldableWithIndex, foldlWithIndex)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Set as Set
import Data.Tuple (fst, snd, uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Unfoldable (class Unfoldable)
import Foreign.Generic (class Decode, class Encode, F, decode, encode)
import Marlowe.Extended.OrderedSet (OrderedSet)
import Marlowe.Extended.OrderedSet as OrderedSet

data OrderedMap a b
  = OrderedMap (Array (a /\ b))

instance eqOrderedMap :: (Eq a, Eq b) => Eq (OrderedMap a b) where
  eq (OrderedMap om1) (OrderedMap om2) = eq om1 om2

instance semigroupOrderedMap :: Ord a => Semigroup (OrderedMap a b) where
  append = appendOrderedMap

instance monoidOrderedMap :: Ord a => Monoid (OrderedMap a b) where
  mempty = OrderedMap mempty

instance foldableOrderedMap :: Foldable (OrderedMap k) where
  foldl f z (OrderedMap m) = Array.foldl f z (map snd m)
  foldr f z (OrderedMap m) = Array.foldr f z (map snd m)
  foldMap f (OrderedMap m) = Array.foldMap f (map snd m)

instance foldableWithIndexOrderedMap :: FoldableWithIndex k (OrderedMap k) where
  foldlWithIndex f z (OrderedMap m) = Array.foldl (uncurry <<< (flip f)) z m
  foldrWithIndex f z (OrderedMap m) = Array.foldr (uncurry f) z m
  foldMapWithIndex f (OrderedMap m) = Array.foldMap (uncurry f) m

instance functorOrderedMap :: Functor (OrderedMap k) where
  map f (OrderedMap m) = OrderedMap (map (rmap f) m)

instance encodeOrderedMap :: (Encode a, Encode b) => Encode (OrderedMap a b) where
  encode (OrderedMap m) = encode m

instance decodeSession :: (Ord a, Decode a, Decode b) => Decode (OrderedMap a b) where
  decode m = fromFoldable <$> ((decode m) :: F (Array (a /\ b)))

instance showOrderedMap :: (Show k, Show v) => Show (OrderedMap k v) where
  show (OrderedMap m) = "(fromFoldable " <> show m <> ")"

isEmpty :: forall k v. OrderedMap k v -> Boolean
isEmpty (OrderedMap om) = Array.null om

singleton :: forall k v. k -> v -> OrderedMap k v
singleton k v = OrderedMap (Array.singleton (k /\ v))

fromFoldable :: forall f k v. Ord k => Foldable f => f (k /\ v) -> OrderedMap k v
fromFoldable = foldMap (uncurry singleton)

fromFoldableWithIndex :: forall f k v. Ord k => FoldableWithIndex k f => f v -> OrderedMap k v
fromFoldableWithIndex = foldlWithIndex (\k m v -> insert k v m) mempty

keys :: forall k v. Ord k => OrderedMap k v -> OrderedSet k
keys (OrderedMap om) = OrderedSet.fromFoldable (map fst om)

filter :: forall k v. Ord k => (v -> Boolean) -> OrderedMap k v -> OrderedMap k v
filter f om = filterWithKey (\k v -> f v) om

filterKeys :: forall k v. Ord k => (k -> Boolean) -> OrderedMap k v -> OrderedMap k v
filterKeys f om = filterWithKey (\k v -> f k) om

filterWithKey :: forall k v. Ord k => (k -> v -> Boolean) -> OrderedMap k v -> OrderedMap k v
filterWithKey f (OrderedMap om) = OrderedMap $ Array.filter (uncurry f) om

appendOrderedMap :: forall k v. Ord k => OrderedMap k v -> OrderedMap k v -> OrderedMap k v
appendOrderedMap om1 om2@(OrderedMap innerOm2) = OrderedMap (innerOm1WithoutOm2 <> innerOm2)
  where
  om2KeySet = Set.fromFoldable $ keys om2

  OrderedMap innerOm1WithoutOm2 = filterKeys (\x -> not $ Set.member x om2KeySet) om1

unionWith :: forall k v. Ord k => (v -> v -> v) -> OrderedMap k v -> OrderedMap k v -> OrderedMap k v
unionWith f om1 om2 = foldMap (\k -> maybe mempty (singleton k) (Map.lookup k fomm)) allKeys
  where
  omm1 = Map.fromFoldableWithIndex om1

  omm2 = Map.fromFoldableWithIndex om2

  fomm = Map.unionWith f omm1 omm2

  k1 = keys om1

  sk1 = Set.fromFoldable k1

  k2 = OrderedSet.filter (\x -> not $ Set.member x sk1) $ keys om2

  allKeys = k1 <> k2

toUnfoldable :: forall f k v. Unfoldable f => OrderedMap k v -> f (k /\ v)
toUnfoldable (OrderedMap m) = Array.toUnfoldable m

insert :: forall k v. Ord k => k -> v -> OrderedMap k v -> OrderedMap k v
insert k v (OrderedMap m) =
  OrderedMap
    ( ( fromMaybe (\_ -> Array.snoc m (k /\ v))
          ( do
              i <- Array.findIndex (\(x /\ _) -> x == k) m
              r <- Array.updateAt i (k /\ v) m
              pure (\_ -> r)
          )
      )
        unit
    ) -- Anonymous function wrapper added to delay computation of the default case

delete :: forall k v. Ord k => k -> OrderedMap k v → OrderedMap k v
delete k om = filterKeys ((/=) k) om

lookup :: forall k v. Ord k => k -> OrderedMap k v -> Maybe v
lookup k (OrderedMap m) = map snd (Array.find (\(k2 /\ _) -> k2 == k) m)

alter :: forall k v. Ord k => (Maybe v -> Maybe v) -> k -> OrderedMap k v -> OrderedMap k v
alter f k om = case mOldValue, mNewValue of
  Nothing, Nothing -> om
  Just _, Nothing -> delete k om
  _, Just x -> insert k x om
  where
  mOldValue = lookup k om

  mNewValue = f mOldValue
