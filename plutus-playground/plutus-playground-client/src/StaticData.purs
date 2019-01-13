module StaticData
  ( demoFiles
  , bufferLocalStorageKey
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import LocalStorage as LocalStorage
import Playground.Usecases (vesting, game, crowdfunding, messages)

type Label = String
type Contents = String

demoFiles :: Map Label Contents
demoFiles =
  Map.fromFoldable
    [ "Crowdfunding" /\ crowdfunding
    , "Game" /\ game
    , "Messages" /\ messages
    , "Vesting" /\ vesting
    ]

bufferLocalStorageKey :: LocalStorage.Key
bufferLocalStorageKey  = LocalStorage.Key "PlutusPlaygroundBuffer"
