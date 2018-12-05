module StaticData
  ( editorContents
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import Playground.Usecases (vesting, game, crowdfunding, messages)

editorContents :: Map String String
editorContents =
  Map.fromFoldable
    [ "Vesting" /\ vesting
    , "Game" /\ game
    , "Crowdfunding" /\ crowdfunding
    , "Messages" /\ messages
    ]
