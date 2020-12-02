-- This event is described here.
-- https://developers.google.com/blockly/guides/configure/web/events#blocklyeventsblock_move
module Blockly.MoveEvent where

import Blockly.Events (unsafePropertyMaybeUndefined, unsafeReadBlocklyEventType)
import Data.Maybe (Maybe)
import Web.Event.Event (Event)

foreign import data MoveEvent :: Type

fromEvent :: Event -> Maybe MoveEvent
fromEvent = unsafeReadBlocklyEventType "move"

-- UUID of new parent block. Nothing if it is a top level block.
newParentId :: MoveEvent -> Maybe String
newParentId = unsafePropertyMaybeUndefined "newParentId"

-- UUID of old parent block. Nothing if it was a top level block.
oldParentId :: MoveEvent -> Maybe String
oldParentId = unsafePropertyMaybeUndefined "oldParentId"

-- Name of input on old parent. Nothing if it was a top level block or parent's next block.
oldInputName :: MoveEvent -> Maybe String
oldInputName = unsafePropertyMaybeUndefined ""

-- Name of input on new parent. Nothing if it is a top level block or parent's next block.
newInputName :: MoveEvent -> Maybe String
newInputName = unsafePropertyMaybeUndefined "newInputName"

{-
If needed these properties are also available
  oldCoordinate	object	X and Y coordinates if it was a top level block. Undefined if it had a parent.
  newCoordinate	object	X and Y coordinates if it is a top level block. Undefined if it has a parent.
  workspaceId	string	UUID of workspace. The workspace can be found with Blockly.Workspace.getById(event.workspaceId)
  blockId	string	UUID of block. The block can be found with workspace.getBlockById(event.blockId)
  group	string	UUID of group. Some events are part of an indivisible group, such as inserting a statement in a stack.
-}
