{-# LANGUAGE CPP #-}

module Data.Aeson.Flatten
  ( flattenObject
  , unflattenObject
  , mergeObject
  , mergeValue
  , objToHm
  , hmToObj
  ) where

import Data.Aeson
#if MIN_VERSION_aeson(2,0,0)
import Data.Aeson.KeyMap
#endif
import Data.HashMap.Strict qualified as HM
import Data.Text qualified as Text

-- | Convert an object to a hashmap. Compatibility shim for pre-/post-aeson-2.
objToHm :: Object -> HM.HashMap Text.Text Value
#if MIN_VERSION_aeson(2,0,0)
objToHm = toHashMapText
#else
objToHm = id
#endif

-- | Convert a hashmap to an object. Compatibility shim for pre-/post-aeson-2.
hmToObj :: HM.HashMap Text.Text Value -> Object
#if MIN_VERSION_aeson(2,0,0)
hmToObj = fromHashMapText
#else
hmToObj = id
#endif

{-| Turn a nested object into a "flat" object where the keys represent paths into the original
object. The keys in the result will be the keys in the original path, separated by `sep`.
The inverse of 'unflattenObject'. -}
flattenObject :: Text.Text -> Object -> Object
flattenObject sep o = hmToObj $ go Nothing (objToHm o)
  where
    go :: Maybe Text.Text -> HM.HashMap Text.Text Value -> HM.HashMap Text.Text Value
    go mprefix = HM.foldMapWithKey $ \k v ->
      let newName = case mprefix of
            Just prefix -> prefix <> sep <> k
            Nothing -> k
       in case v of
            Object o' -> go (Just newName) $ objToHm o'
            leaf -> HM.singleton newName leaf

{-| Turn a "flat" object whose keys represent paths into an unflattened object.
The keys in the result will be the resulting path, separated by `sep`.
The inverse of 'flattenObject'. -}
unflattenObject :: Text.Text -> Object -> Object
unflattenObject sep o =
  HM.foldlWithKey (\acc k v -> mergeObject acc (mkPathObject k v)) mempty (objToHm o)
  where
    mkPathObject :: Text.Text -> Value -> Object
    mkPathObject k value =
      let path = Text.splitOn sep k
       in hmToObj $ go path value
      where
        go :: [Text.Text] -> Value -> HM.HashMap Text.Text Value
        go [] _ = error "empty path"
        go [n] v = HM.singleton n v
        go (n : n' : xs) v = HM.singleton n $ Object $ hmToObj $ go (n' : xs) v

{-| Merge two objects, merging the values where both sides have an entry for a key rather than
taking the first. -}
mergeObject :: Object -> Object -> Object
mergeObject o1 o2 = hmToObj $ HM.unionWith mergeValue (objToHm o1) (objToHm o2)

-- | Merge two values, merging the objects using 'mergeObject'. Can't merge anything else.
mergeValue :: Value -> Value -> Value
mergeValue (Object o1) (Object o2) = Object $ mergeObject o1 o2
mergeValue _ _ = error "can't merge"
