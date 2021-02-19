module Data.Map.Extra
  ( mapIndex
  , findIndex
  ) where

import Prelude
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex)
import Data.Map (Map, keys, singleton)
import Data.Maybe (Maybe)
import Data.Set (filter, findMin)

mapIndex :: forall f v k1 k2. FoldableWithIndex k1 f => Ord k2 => (k1 -> k2) -> f v -> Map k2 v
mapIndex f = foldMapWithIndex (\k v -> singleton (f k) v)

findIndex :: forall k v. Ord k => (k -> Boolean) -> Map k v -> Maybe k
findIndex f map = findMin $ filter f $ keys map
