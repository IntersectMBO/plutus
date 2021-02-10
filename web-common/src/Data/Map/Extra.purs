module Data.Map.Extra (mapIndex) where

import Prelude
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex)
import Data.Map (Map, singleton)

mapIndex :: forall f v k1 k2. FoldableWithIndex k1 f => Ord k2 => (k1 -> k2) -> f v -> Map k2 v
mapIndex f = foldMapWithIndex (\k v -> singleton (f k) v)
