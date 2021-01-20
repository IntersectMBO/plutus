module Blockly.Events
  ( class HasEvent
  , fromEvent
  , CreateEvent
  , ChangeEvent
  , FinishLoadingEvent
  , MoveEvent
  , UIEvent
  , newParentId
  , oldParentId
  , oldInputName
  , newInputName
  ) where

import Data.Maybe (Maybe(..))
import Data.Function.Uncurried (Fn4, runFn4)
import Web.Event.Event (Event)

class HasEvent a where
  fromEvent :: Event -> Maybe a

-- This events are described here. For the moment we only care about it's type, but we could
-- get more properties
-- https://developers.google.com/blockly/guides/configure/web/events
foreign import data CreateEvent :: Type

instance hasEventCreateEvent :: HasEvent CreateEvent where
  fromEvent :: Event -> Maybe CreateEvent
  fromEvent = readBlocklyEventType "create"

------------------------------------------------------------
foreign import data ChangeEvent :: Type

instance hasEventChangeEvent :: HasEvent ChangeEvent where
  fromEvent :: Event -> Maybe ChangeEvent
  fromEvent = readBlocklyEventType "change"

------------------------------------------------------------
foreign import data UIEvent :: Type

instance hasEventUIEvent :: HasEvent UIEvent where
  fromEvent :: Event -> Maybe UIEvent
  fromEvent = readBlocklyEventType "ui"

------------------------------------------------------------
foreign import data FinishLoadingEvent :: Type

instance hasEventFinishLoadingEvent :: HasEvent FinishLoadingEvent where
  fromEvent :: Event -> Maybe FinishLoadingEvent
  fromEvent = readBlocklyEventType "finished_loading"

------------------------------------------------------------
foreign import data MoveEvent :: Type

instance hasEventMoveEvent :: HasEvent MoveEvent where
  fromEvent :: Event -> Maybe MoveEvent
  fromEvent = readBlocklyEventType "move"

-- UUID of new parent block. Nothing if it is a top level block.
newParentId :: MoveEvent -> Maybe String
newParentId = readProperty "newParentId"

-- UUID of old parent block. Nothing if it was a top level block.
oldParentId :: MoveEvent -> Maybe String
oldParentId = readProperty "oldParentId"

-- Name of input on old parent. Nothing if it was a top level block or parent's next block.
oldInputName :: MoveEvent -> Maybe String
oldInputName = readProperty "oldInputName"

-- Name of input on new parent. Nothing if it is a top level block or parent's next block.
newInputName :: MoveEvent -> Maybe String
newInputName = readProperty "newInputName"

{-
If needed these properties are also available for MoveEvent
  oldCoordinate	object	X and Y coordinates if it was a top level block. Undefined if it had a parent.
  newCoordinate	object	X and Y coordinates if it is a top level block. Undefined if it has a parent.
  workspaceId	string	UUID of workspace. The workspace can be found with Blockly.Workspace.getById(event.workspaceId)
  blockId	string	UUID of block. The block can be found with workspace.getBlockById(event.blockId)
  group	string	UUID of group. Some events are part of an indivisible group, such as inserting a statement in a stack.
-}
------------------------------------------------------------
-- This function let us check if a blockly event is of the desired type. It was inspired by unsafeReadProtoTagged
-- and the reason it's unsafe, it's because there could be other objects that have a property called `type` with
-- the appropiate value, but may not have the correct shape.
-- https://pursuit.purescript.org/packages/purescript-web-events/2.0.1/docs/Web.Internal.FFI#v:unsafeReadProtoTagged
readBlocklyEventType :: forall a b. String -> a -> Maybe b
readBlocklyEventType name value = runFn4 _readBlocklyEventType Nothing Just name value

foreign import _readBlocklyEventType ::
  forall a b.
  Fn4
    (forall x. Maybe x)
    (forall x. x -> Maybe x)
    String
    a
    (Maybe b)

-- Similar to the above, this function expects to receive a Blockly event and a property that may be undefined
-- for example "newParentId" and return the property in a maybe
readProperty :: forall a b. String -> a -> Maybe b
readProperty property event = runFn4 _readProperty Nothing Just property event

foreign import _readProperty ::
  forall a b.
  Fn4
    (forall x. Maybe x)
    (forall x. x -> Maybe x)
    String
    a
    (Maybe b)
