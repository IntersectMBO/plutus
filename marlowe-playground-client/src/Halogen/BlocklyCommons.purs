-- TODO In a different commit I'd rename Blockly to BlocklyEditor and ActusBlockly as ActusEditor or
-- ActusBlocklyEditor and this module could be called solely Blockly
module Halogen.BlocklyCommons where

import Prelude hiding (div)
import Blockly (addChangeListener, removeChangeListener)
import Blockly.Events (fromEvent, newParentId, oldParentId)
import Blockly.Types (BlocklyEvent, Workspace)
import Blockly.Types as BT
import Data.Foldable (oneOf)
import Data.Lens (Lens', assign)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Data.Traversable (for_)
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, raise)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
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
      eventListener \event ->
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
        in
          for_ mEvent \ev -> EventSource.emit emitter (toAction ev)
    addChangeListener workspace listener
    pure $ EventSource.Finalizer $ removeChangeListener workspace listener

_hasUnsavedChanges' :: forall r. Lens' { hasUnsavedChanges :: Boolean | r } Boolean
_hasUnsavedChanges' = prop (SProxy :: SProxy "hasUnsavedChanges")

updateUnsavedChangesActionHandler ::
  forall m state action slots message.
  MonadAff m =>
  message ->
  message ->
  BlocklyEvent ->
  HalogenM { hasUnsavedChanges :: Boolean | state } action slots message m Unit
updateUnsavedChangesActionHandler codeChange finishLoading event = do
  let
    setUnsavedChangesToTrue = do
      assign _hasUnsavedChanges' true
      raise codeChange
  case event of
    (BT.Change _) -> setUnsavedChangesToTrue
    -- The move event only changes the unsaved status if the parent has changed (either by attaching or detaching
    -- one block into another)
    (BT.Move ev) -> when (newParentId ev /= oldParentId ev) setUnsavedChangesToTrue
    (BT.FinishLoading _) -> do
      assign _hasUnsavedChanges' false
      raise finishLoading
    -- The create event by itself does not modify the contract. It is modified once it's attached or detached
    -- from a parent, and that is covered by the Move event
    (BT.Create _) -> pure unit
