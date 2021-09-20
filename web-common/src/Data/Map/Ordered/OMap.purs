module Data.Map.Ordered.OMap (OMap, alter, delete, fromFoldable, fromFoldableWithIndex, insert, isEmpty, keys, lookup, singleton, toUnfoldable, unionWith) where

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
import Data.Set.Ordered.OSet (OSet)
import Data.Set.Ordered.OSet as OSet

newtype OMap a b
  = OMap (Array (a /\ b))

instance eqOMap :: (Eq a, Eq b) => Eq (OMap a b) where
  eq (OMap om1) (OMap om2) = eq om1 om2

instance semigroupOMap :: Ord a => Semigroup (OMap a b) where
  append = appendOMap

instance monoidOMap :: Ord a => Monoid (OMap a b) where
  mempty = OMap mempty

instance foldableOMap :: Foldable (OMap k) where
  foldl f z (OMap m) = Array.foldl f z (map snd m)
  foldr f z (OMap m) = Array.foldr f z (map snd m)
  foldMap f (OMap m) = Array.foldMap f (map snd m)

instance foldableWithIndexOMap :: FoldableWithIndex k (OMap k) where
  foldlWithIndex f z (OMap m) = Array.foldl (uncurry <<< (flip f)) z m
  foldrWithIndex f z (OMap m) = Array.foldr (uncurry f) z m
  foldMapWithIndex f (OMap m) = Array.foldMap (uncurry f) m

instance functorOMap :: Functor (OMap k) where
  map f (OMap m) = OMap (map (rmap f) m)

instance encodeOMap :: (Encode a, Encode b) => Encode (OMap a b) where
  encode (OMap m) = encode m

instance decodeSession :: (Ord a, Decode a, Decode b) => Decode (OMap a b) where
  decode m = fromFoldable <$> ((decode m) :: F (Array (a /\ b)))

instance showOMap :: (Show k, Show v) => Show (OMap k v) where
  show (OMap m) = "(fromFoldable " <> show m <> ")"

isEmpty :: forall k v. OMap k v -> Boolean
isEmpty (OMap om) = Array.null om

singleton :: forall k v. k -> v -> OMap k v
singleton k v = OMap (Array.singleton (k /\ v))

fromFoldable :: forall f k v. Ord k => Foldable f => f (k /\ v) -> OMap k v
fromFoldable = foldMap (uncurry singleton)

fromFoldableWithIndex :: forall f k v. Ord k => FoldableWithIndex k f => f v -> OMap k v
fromFoldableWithIndex = foldlWithIndex (\k m v -> insert k v m) mempty

keys :: forall k v. Ord k => OMap k v -> OSet k
keys (OMap om) = OSet.fromFoldable (map fst om)

filter :: forall k v. Ord k => (v -> Boolean) -> OMap k v -> OMap k v
filter f om = filterWithKey (\k v -> f v) om

filterKeys :: forall k v. Ord k => (k -> Boolean) -> OMap k v -> OMap k v
filterKeys f om = filterWithKey (\k v -> f k) om

filterWithKey :: forall k v. Ord k => (k -> v -> Boolean) -> OMap k v -> OMap k v
filterWithKey f (OMap om) = OMap $ Array.filter (uncurry f) om

appendOMap :: forall k v. Ord k => OMap k v -> OMap k v -> OMap k v
appendOMap om1 om2@(OMap innerOm2) = OMap (innerOm1WithoutOm2 <> innerOm2)
  where
  om2KeySet = Set.fromFoldable $ keys om2

  OMap innerOm1WithoutOm2 = filterKeys (\x -> not $ Set.member x om2KeySet) om1

unionWith :: forall k v. Ord k => (v -> v -> v) -> OMap k v -> OMap k v -> OMap k v
unionWith f om1 om2 = foldMap (\k -> maybe mempty (singleton k) (Map.lookup k fomm)) allKeys
  where
  omm1 = Map.fromFoldableWithIndex om1

  omm2 = Map.fromFoldableWithIndex om2

  fomm = Map.unionWith f omm1 omm2

  k1 = keys om1

  sk1 = Set.fromFoldable k1

  k2 = OSet.filter (\x -> not $ Set.member x sk1) $ keys om2

  allKeys = k1 <> k2

toUnfoldable :: forall f k v. Unfoldable f => OMap k v -> f (k /\ v)
toUnfoldable (OMap m) = Array.toUnfoldable m

insert :: forall k v. Ord k => k -> v -> OMap k v -> OMap k v
insert k v (OMap m) =
  OMap
    ( ( fromMaybe (\_ -> Array.snoc m (k /\ v))
          ( do
              i <- Array.findIndex (\(x /\ _) -> x == k) m
              r <- Array.updateAt i (k /\ v) m
              pure (\_ -> r)
          )
      )
        unit
    ) -- Anonymous function wrapper added to delay computation of the default case

delete :: forall k v. Ord k => k -> OMap k v → OMap k v
delete k om = filterKeys ((/=) k) om

lookup :: forall k v. Ord k => k -> OMap k v -> Maybe v
lookup k (OMap m) = map snd (Array.find (\(k2 /\ _) -> k2 == k) m)

alter :: forall k v. Ord k => (Maybe v -> Maybe v) -> k -> OMap k v -> OMap k v
alter f k om = case mOldValue, mNewValue of
  Nothing, Nothing -> om
  Just _, Nothing -> delete k om
  _, Just x -> insert k x om
  where
  mOldValue = lookup k om

  mNewValue = f mOldValue
