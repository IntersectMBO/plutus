-- This event is described here. For the moment we only care about it's type, but we could
-- get more properties
-- https://developers.google.com/blockly/guides/configure/web/events#blocklyeventsblock_create
module Blockly.CreateEvent where

import Blockly.Events (unsafeReadBlocklyEventType)
import Data.Maybe (Maybe)
import Web.Event.Event (Event)

foreign import data CreateEvent :: Type

fromEvent :: Event -> Maybe CreateEvent
fromEvent = unsafeReadBlocklyEventType "create"
