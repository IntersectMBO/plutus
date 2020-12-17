-- | foreign types are only mutated in the ST monad. This means we must only
--   export foreign functions that mutate if they act on STRefs
--   Within the rest of the purescript code we cannot change these values anyway
--   since they are foreign so it's crucial that we are correct with the foreign
--   function types
module Blockly.Types where

import Blockly.Events (ChangeEvent, CreateEvent, FinishLoadingEvent, MoveEvent)

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
