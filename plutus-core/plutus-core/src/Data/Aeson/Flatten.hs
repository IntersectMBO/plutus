module Data.Aeson.Flatten
    ( flattenObject
    , unflattenObject
    , mergeObject
    , mergeValue
    ) where

import           Data.Aeson
import qualified Data.HashMap.Strict as HM
import qualified Data.Text           as Text

-- | Turn a nested object into a "flat" object where the keys represent paths into the original object. The keys in the result
-- will be the keys in the original path, separated by `sep`. The inverse of 'unflattenObject'.
flattenObject :: Text.Text -> Object -> Object
flattenObject sep = go Nothing
    where
        go :: Maybe Text.Text -> Object -> Object
        go mprefix = HM.foldMapWithKey $ \k v ->
            let newName = case mprefix of
                    Just prefix -> prefix <> sep <> k
                    Nothing     -> k
            in case v of
                Object o -> go (Just newName) o
                leaf     -> HM.singleton newName leaf

-- | Turn a "flat" object whose keys represent paths into an unflattened object. The keys in the result will be the
-- resulting path, separated by `sep`. The inverse of 'flattenObject'.
unflattenObject :: Text.Text -> Object -> Object
unflattenObject sep = HM.foldlWithKey (\acc k v -> mergeObject acc (mkPathObject k v)) mempty
    where
        mkPathObject :: Text.Text -> Value -> Object
        mkPathObject k value =
            let path = Text.splitOn sep k
            in go path value
            where
                go :: [Text.Text] -> Value -> Object
                go [] _        = error "empty path"
                go [n] v       = HM.singleton n v
                go (n:n':xs) v = HM.singleton n $ Object $ go (n':xs) v

-- | Merge two objects, merging the values where both sides have an entry for a key rather than taking the first.
mergeObject :: Object -> Object -> Object
mergeObject = HM.unionWith mergeValue

-- | Merge two values, merging the objects using 'mergeObject'. Can't merge anything else.
mergeValue :: Value -> Value -> Value
mergeValue (Object o1) (Object o2) = Object $ mergeObject o1 o2
mergeValue _ _                     = error "can't merge"
