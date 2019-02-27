module StaticData
  ( demoFiles
  , bufferLocalStorageKey
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import LocalStorage as LocalStorage
import Meadow.Contracts (basicContract)

type Label = String
type Contents = String

demoFiles :: Map Label Contents
demoFiles =
  Map.fromFoldable
    [ "BasicContract" /\ basicContract
    ]

bufferLocalStorageKey :: LocalStorage.Key
bufferLocalStorageKey  = LocalStorage.Key "PlutusPlaygroundBuffer"
