module StaticData
  ( demoFiles
  , bufferLocalStorageKey
  , marloweBufferLocalStorageKey
  , marloweContracts
  , marloweContract
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import LocalStorage as LocalStorage
import Marlowe.Contracts (crowdFunding, depositInsentive, escrow)
import Meadow.Contracts (basicContract)

type Label = String
type Contents = String

demoFiles :: Map Label Contents
demoFiles =
  Map.fromFoldable
    [ "BasicContract" /\ basicContract
    ]

marloweContracts :: Map Label Contents
marloweContracts =
  Map.fromFoldable
    [ "Deposit Insentive" /\ depositInsentive
    , "Crowd Funding" /\ crowdFunding
    , "Escrow" /\ escrow
    ]

marloweContract :: Contents
marloweContract = "(Some Marlowe Code)"

bufferLocalStorageKey :: LocalStorage.Key
bufferLocalStorageKey  = LocalStorage.Key "PlutusPlaygroundBuffer"

marloweBufferLocalStorageKey :: LocalStorage.Key
marloweBufferLocalStorageKey = LocalStorage.Key "MarloweBuffer"
