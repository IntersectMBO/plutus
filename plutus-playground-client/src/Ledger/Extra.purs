module Ledger.Extra where

import Prelude

import Data.Array as Array
import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex)
import Data.Generic (class Generic, gShow)
import Data.Lens (Lens', lens, wander)
import Data.Lens.At (class At)
import Data.Lens.Index (class Index)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Monoid (class Monoid)
import Data.Newtype (class Newtype, unwrap)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Data.Tuple.Nested (type (/\), (/\))

newtype LedgerMap k v = LedgerMap (Array (Tuple k v))

derive instance genericLedgerMap :: (Generic k, Generic v) => Generic (LedgerMap k v)
derive instance newtypeLedgerMap :: Newtype (LedgerMap k v) _

instance eqLedgerMap :: (Ord k, Eq v) => Eq (LedgerMap k v) where
  eq (LedgerMap xs) (LedgerMap ys) =
    Array.sortWith fst xs == Array.sortWith fst ys

instance showValue :: (Generic k, Generic v, Show k, Show v) => Show (LedgerMap k v) where
  show = gShow

_LedgerMap :: forall k v. Lens' (LedgerMap k v) (Array (Tuple k v))
_LedgerMap = _Newtype

-- | Compute the union of two `LedgerMap`s, using the specified function to combine values for duplicate keys.
-- Notes:
--   This function does not offer any guarantees about ordering.
--   `LedgerMap`s may themselves contain duplicate keys, and they too will be combined with the specified function.
unionWith :: forall k v. Ord k => (v -> v -> v) -> LedgerMap k v -> LedgerMap k v -> LedgerMap k v
unionWith f (LedgerMap a) (LedgerMap b) =
  LedgerMap $
  Map.toUnfoldable $
  Map.unionWith f
    (Map.fromFoldableWith f a)
    (Map.fromFoldableWith f b)

instance semigroupLedgerMap :: (Ord k, Semigroup v) => Semigroup (LedgerMap k v) where
  append = unionWith append

instance monoidLedgerMap :: (Ord k, Semigroup v) => Monoid (LedgerMap k v) where
  mempty = LedgerMap []

null :: forall k v. LedgerMap k v -> Boolean
null = unwrap >>> Array.null

instance foldableLedgerMap :: Foldable (LedgerMap k) where
  foldMap f = foldMap (f <<< snd) <<< unwrap
  foldl f z = foldl (\b -> f b <<< snd) z <<< unwrap
  foldr f z = foldr (\x b -> f (snd x) b) z <<< unwrap

instance foldableWithIndexLedgerMap :: FoldableWithIndex k (LedgerMap k) where
  foldMapWithIndex f = foldMap (uncurry f) <<< unwrap
  foldlWithIndex f z = foldl (\acc (Tuple k v) -> f k acc v) z <<< unwrap
  foldrWithIndex f z = foldr (\(Tuple k v) acc -> f k v acc) z <<< unwrap

instance indexLedgerMap :: Eq k => Index (LedgerMap k a) k a where
  ix key = wander \f (LedgerMap values) ->
    map LedgerMap
    $ sequence
    $ map (\(Tuple k v) ->
            Tuple k <$> (if k == key
                         then f
                         else pure) v
          ) values

instance atLedgerMap :: Eq k => At (LedgerMap k a) k a where
  at key = lens get set
    where
      matching tuple = fst tuple == key
      get (LedgerMap xs) = map snd $ Array.find matching xs
      set (LedgerMap xs) Nothing = LedgerMap $ Array.filter (not matching) xs
      set (LedgerMap []) (Just new) = LedgerMap [ Tuple key new ]
      set (LedgerMap xs) (Just new) =
        case Array.findIndex matching xs of
          Nothing -> LedgerMap $ Array.snoc xs (Tuple key new)
          _ -> LedgerMap $ map (\(Tuple k v) ->
                                 Tuple k (if k == key
                                          then new
                                          else v)) xs

collapse ::
  forall m n i j a.
  FoldableWithIndex i m
  => FoldableWithIndex j n
  => m (n a)
  -> Array (i /\ j /\ a)
collapse =
  foldMapWithIndex (\i -> foldMapWithIndex (\j a -> [ i /\ j /\ a ]))
