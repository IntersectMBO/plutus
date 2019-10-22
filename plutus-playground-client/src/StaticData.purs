module StaticData
  ( demoFiles
  , bufferLocalStorageKey
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import LocalStorage as LocalStorage
import Playground.Usecases (vesting, game, crowdfunding, errorHandling, starter)

type Label
  = String

type Contents
  = String

demoFiles :: Map Label Contents
demoFiles =
  Map.fromFoldable
    [ "Crowdfunding" /\ crowdfunding
    , "Game" /\ game
    , "Error Handling" /\ errorHandling
    , "Vesting" /\ vesting
    , "Starter" /\ starter
    ]

bufferLocalStorageKey :: LocalStorage.Key
bufferLocalStorageKey = LocalStorage.Key "PlutusPlaygroundBuffer"
