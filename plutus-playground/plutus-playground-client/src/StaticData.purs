module StaticData
  ( editorContents
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import Playground.Usecases (vesting, game, crowdfunding, messages)

type Label = String
type Contents = String

editorContents :: Map Label Contents
editorContents =
  Map.fromFoldable
    [ "Crowdfunding" /\ crowdfunding
    , "Game" /\ game
    , "Messages" /\ messages
    , "Vesting" /\ vesting
    ]
