module Data.Map.Lens where

import Prelude
import Data.Lens (Getter', to)
import Data.Map (Map)
import Data.Map as Map

_MaxIndex :: forall k v. Getter' (Map k v) Int
_MaxIndex = to Map.size

_NextIndex :: forall k v. Getter' (Map k v) Int
_NextIndex = to Map.size <<< to (add one)
