module StaticData
  ( demoFiles
  , bufferLocalStorageKey
  , marloweBufferLocalStorageKey
  , marloweContract
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

marloweContract :: Contents
marloweContract = "(Some Marlowe Code)"

bufferLocalStorageKey :: LocalStorage.Key
bufferLocalStorageKey  = LocalStorage.Key "PlutusPlaygroundBuffer"

marloweBufferLocalStorageKey :: LocalStorage.Key
marloweBufferLocalStorageKey = LocalStorage.Key "MarloweBuffer"
