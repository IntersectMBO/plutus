module Language.PlutusTx.AssocMap where

import Prelude
import AjaxUtils (defaultJsonOptions)
import Data.Array as Array
import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex)
import Data.Function (on)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Json.JsonTuple (JsonTuple(..))
import Data.Lens (Iso', lens, wander)
import Data.Lens.At (class At)
import Data.Lens.Index (class Index)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as Data.Map
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Newtype as Newtype
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Foreign.Class (class Decode, class Encode)
import Foreign.Generic (genericDecode, genericEncode)

newtype Map a b
  = Map (Array (JsonTuple a b))

keys :: forall k v. Ord k => Map k v -> Set k
keys (Map entries) = Set.fromFoldable $ map (fst <<< unwrap) entries

derive instance functorMap :: Functor (Map a)

instance encodeMap :: (Encode a, Encode b) => Encode (Map a b) where
  encode value = genericEncode defaultJsonOptions value

instance decodeMap :: (Decode a, Decode b) => Decode (Map a b) where
  decode value = genericDecode defaultJsonOptions value

derive instance genericMap :: Generic (Map a b) _

derive instance newtypeMap :: Newtype (Map a b) _

instance eqMap :: (Ord k, Eq k, Eq v) => Eq (Map k v) where
  eq = eq `on` (Data.Map.fromFoldable <<< map unwrap <<< unwrap)

--------------------------------------------------------------------------------
_Map :: forall a b. Iso' (Map a b) (Array (JsonTuple a b))
_Map = _Newtype

instance showMap :: (Show k, Show v) => Show (Map k v) where
  show x = genericShow x

instance foldableMap :: Foldable (Map k) where
  foldMap f = foldMap (f <<< snd) <<< toTuples
  foldl f z = foldl (\b -> f b <<< snd) z <<< toTuples
  foldr f z = foldr (\x b -> f (snd x) b) z <<< toTuples

instance foldableWithIndexMap :: FoldableWithIndex k (Map k) where
  foldMapWithIndex f = foldMap (uncurry f) <<< toTuples
  foldlWithIndex f z = foldl (\acc (Tuple k v) -> f k acc v) z <<< toTuples
  foldrWithIndex f z = foldr (\(Tuple k v) acc -> f k v acc) z <<< toTuples

instance indexMap :: Eq k => Index (Map k a) k a where
  ix key =
    wander \f (Map values) ->
      map Map
        $ sequence
        $ map
            ( Newtype.traverse JsonTuple
                ( \(Tuple k v) ->
                    Tuple k <$> (if k == key then f v else pure v)
                )
            )
            values

instance atMap :: Eq k => At (Map k a) k a where
  at key = lens get set
    where
    matching (JsonTuple tuple) = fst tuple == key

    get (Map xs) = map (snd <<< unwrap) $ Array.find matching xs

    set (Map xs) Nothing = Map $ Array.filter (not matching) $ xs

    set (Map xs) (Just new) =
      Map
        $ case Array.findIndex matching xs of
            Nothing -> Array.snoc xs (JsonTuple (Tuple key new))
            _ ->
              map
                ( Newtype.over JsonTuple
                    ( \(Tuple k v) ->
                        Tuple k (if k == key then new else v)
                    )
                )
                xs

toTuples :: forall k v. Map k v -> Array (Tuple k v)
toTuples = map unwrap <<< unwrap

fromTuples :: forall k v. Array (Tuple k v) -> Map k v
fromTuples = Map <<< map wrap

null :: forall k v. Map k v -> Boolean
null = Array.null <<< unwrap

-- | Compute the union of two `AssocMaps`s, using the specified function to combine values for duplicate keys.
-- Notes:
--
--   * This function does not offer any guarantees about ordering.
--   * `AssocMap`s may themselves contain duplicate keys, and so the
--     same key may appear several times in *both* input `AssocMap`s. They
--     too will be combined with the given function. Thus the
--     resulting `AssocMap` will have unique keys.
unionWith :: forall k v. Ord k => (v -> v -> v) -> Map k v -> Map k v -> Map k v
unionWith f a b =
  fromTuples
    $ Data.Map.toUnfoldable
    $ on (Data.Map.unionWith f) (Data.Map.fromFoldableWith f <<< toTuples)
        a
        b

instance semigroupMap :: (Ord k, Semigroup v) => Semigroup (Map k v) where
  append = unionWith append

instance monoidMap :: (Ord k, Semigroup v) => Monoid (Map k v) where
  mempty = Map mempty

toDataMap :: forall k v. Ord k => Map k v -> Data.Map.Map k v
toDataMap (Map m) = Data.Map.fromFoldable (unwrap <$> m)
