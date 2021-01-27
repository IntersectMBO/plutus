module Blockly.Types where

import Blockly.Events (ChangeEvent, CreateEvent, FinishLoadingEvent, MoveEvent, UIEvent)

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
