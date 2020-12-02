-- This event is described here. For the moment we only care about it's type, but we could
-- get more properties
-- https://developers.google.com/blockly/guides/configure/web/events#blocklyeventsblock_change
module Blockly.FinishLoadingEvent where

import Blockly.Events (unsafeReadBlocklyEventType)
import Data.Maybe (Maybe)
import Web.Event.Event (Event)

foreign import data FinishLoadingEvent :: Type

fromEvent :: Event -> Maybe FinishLoadingEvent
fromEvent = unsafeReadBlocklyEventType "finished_loading"
