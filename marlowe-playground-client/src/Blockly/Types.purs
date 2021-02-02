module Blockly.Types where

import Prelude
import Blockly.Events (ChangeEvent, CreateEvent, FinishLoadingEvent, MoveEvent, UIEvent, element)
import Data.Maybe (Maybe(..))

foreign import data Blockly :: Type

foreign import data Workspace :: Type

foreign import data Block :: Type

type BlocklyState
  = { blockly :: Blockly
    , workspace :: Workspace
    , rootBlockName :: String
    }

data BlocklyEvent
  = Change ChangeEvent
  | Create CreateEvent
  | Move MoveEvent
  | FinishLoading FinishLoadingEvent
  | UI UIEvent

isDragStart :: BlocklyEvent -> Boolean
isDragStart (UI event) = eq (Just "dragStart") $ element event

isDragStart _ = false

isDragStop :: BlocklyEvent -> Boolean
isDragStop (UI event) = eq (Just "dragStop") $ element event

isDragStop _ = false
