module Data.Set.Extra where

import Prelude
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple.Nested ((/\))

-- TODO: There is a function called toMap in version 2.0 of ordered-collections which is more performant as
--       it just extracts the inner representation, but we'll need to upgrade to PS 0.14 to use it
--       https://github.com/purescript/purescript-ordered-collections/blob/master/CHANGELOG.md#v200---2021-02-26
setToMap :: forall a. Ord a => Set a -> Map a Unit
setToMap = Map.fromFoldable <<< Set.map (\key -> key /\ unit)
