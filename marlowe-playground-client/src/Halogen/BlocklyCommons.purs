-- TODO In a different commit I'd rename Blockly to BlocklyEditor and ActusBlockly as ActusEditor or
-- ActusBlocklyEditor and this module could be called solely Blockly
module Halogen.BlocklyCommons where

import Blockly (addChangeListener, removeChangeListener)
import Blockly.Events (MoveEvent, fromEvent, newParentId, oldParentId)
import Blockly.Types (BlocklyEvent, Workspace)
import Blockly.Types as BT
import Control.Alt ((<|>))
import Data.Foldable (oneOf)
import Data.Maybe (maybe)
import Data.Traversable (for_)
import Effect.Aff.Class (class MonadAff)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import Prelude (bind, const, discard, pure, ($), (<$>))
import Web.Event.EventTarget (eventListener)

blocklyEvents ::
  forall m action.
  MonadAff m =>
  (BlocklyEvent -> action) ->
  Workspace ->
  EventSource m action
blocklyEvents toAction workspace =
  EventSource.effectEventSource \emitter -> do
    listener <-
      eventListener \event -> do
        let
          mEvent =
            -- Blockly can fire all of the following events https://developers.google.com/blockly/guides/configure/web/events
            -- but at the moment we only care for the ones that may affect the unsaved changes.
            oneOf
              [ BT.Create <$> fromEvent event
              , BT.Move <$> fromEvent event
              , BT.Change <$> fromEvent event
              , BT.FinishLoading <$> fromEvent event
              ]
        for_ mEvent \ev -> EventSource.emit emitter (toAction ev)
    addChangeListener workspace listener
    pure $ EventSource.Finalizer $ removeChangeListener workspace listener

-- Indicates if a Move Event meant that a block has been attached or detached from another block.
attachesOrDetachesABlock :: MoveEvent -> Boolean
attachesOrDetachesABlock ev = maybe false (const true) $ newParentId ev <|> oldParentId ev
