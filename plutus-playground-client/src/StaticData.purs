module StaticData
  ( demoFiles
  , bufferLocalStorageKey
  ) where

import Data.Tuple.Nested (type (/\), (/\))
import LocalStorage as LocalStorage
import Playground.Usecases (vesting, game, crowdfunding, errorHandling, starter)

type Label
  = String

type Contents
  = String

-- | This would be a `Map`, were it not for the fact that we want a
-- certain key ordering. (Simpler examples first.)
demoFiles :: Array (Label /\ Contents)
demoFiles =
  [ "Starter" /\ starter
  , "Game" /\ game
  , "Vesting" /\ vesting
  , "Crowdfunding" /\ crowdfunding
  , "Error Handling" /\ errorHandling
  ]

bufferLocalStorageKey :: LocalStorage.Key
bufferLocalStorageKey = LocalStorage.Key "PlutusPlaygroundBuffer"
