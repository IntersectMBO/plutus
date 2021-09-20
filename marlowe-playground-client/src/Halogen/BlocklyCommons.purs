-- TODO In a different commit I'd rename Blockly to BlocklyEditor and ActusBlockly as ActusEditor or
-- ActusBlocklyEditor and this module could be called solely Blockly
module Halogen.BlocklyCommons where

import Prelude hiding (div)
import Blockly.Events (fromEvent, newParentId, oldParentId)
import Blockly.Internal (addChangeListener, removeChangeListener)
import Blockly.Types (BlocklyEvent, BlocklyState, Workspace, isDragStart, isDragStop)
import Blockly.Types as BT
import Data.Either (Either(..))
import Data.Foldable (foldl, oneOf)
import Data.Lens (Lens', assign, use)
import Data.Lens.Record (prop)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Data.Traversable (for_)
import Effect (Effect)
import Effect.Aff (Aff, finally, makeAff, nonCanceler)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Timer (clearTimeout, setTimeout)
import Halogen (HalogenM, SubscriptionId)
import Halogen as H
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import Web.Event.EventTarget (EventListener, eventListener)

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
            -- but at the moment we only care for the following ones
            oneOf
              [ BT.Create <$> fromEvent event
              , BT.Move <$> fromEvent event
              , BT.Change <$> fromEvent event
              , BT.FinishLoading <$> fromEvent event
              , BT.UI <$> fromEvent event
              , BT.Select <$> fromEvent event
              ]
        in
          for_ mEvent \ev -> EventSource.emit emitter (toAction ev)
    addChangeListener workspace listener
    pure $ EventSource.Finalizer $ removeChangeListener workspace listener

_eventsWhileDragging :: forall state. Lens' { eventsWhileDragging :: Maybe (List BlocklyEvent) | state } (Maybe (List BlocklyEvent))
_eventsWhileDragging = prop (SProxy :: SProxy "eventsWhileDragging")

-- | Using the blockly events, detect when the contract has changed and fire a halogen message.
-- |
-- | There are two events that signal us that the contract has changed.
-- |   * When the Change event is fired (which means that a property inside a block has changed)
-- |   * When the Move event is fired and the old and new parent are different (which means that
-- |     a block has been attached/detached)
-- |
-- | We also need to track the UI events to see if we are in the middle of a drag-n-drop.
-- | When we attach a block into a new parent there is no problem, but when we detach a block there
-- | is a small inconsistency.
-- | When we start draging a block outside from its parent, Blockly will fire the Move event and let us
-- | believe that the contract has changed. But if we ask Blockly to generate the contract at that point,
-- | the result will include the block we just detached. So we need to accumulate the events fired during
-- | drag-n-drop and analyze them once we drop it.
detectCodeChanges ::
  forall m state action slots message.
  MonadAff m =>
  message ->
  BlocklyEvent ->
  HalogenM { eventsWhileDragging :: Maybe (List BlocklyEvent) | state } action slots message m Unit
detectCodeChanges codeChange event = do
  mDraggingEvents <- use _eventsWhileDragging
  case mDraggingEvents of
    Nothing ->
      -- If we are not inside a drag and drop, let's evaluate the event directly
      if (doesEventModifiesContract event) then
        H.raise codeChange
      else
        -- If the event starts a drag and drop, store it in the state
        when (isDragStart event) $ assign _eventsWhileDragging (Just Nil)
    Just eventsWhileDragging ->
      -- If we are inside a drag and drop, accumulate the events and analyze them all together
      if (not $ isDragStop event) then
        assign _eventsWhileDragging (Just (event : eventsWhileDragging))
      else do
        let
          hasChanged = foldl (\accu ev -> accu || doesEventModifiesContract ev) false eventsWhileDragging
        when hasChanged $ H.raise codeChange
        assign _eventsWhileDragging Nothing
  where
  doesEventModifiesContract :: BlocklyEvent -> Boolean
  doesEventModifiesContract = case _ of
    (BT.Change _) -> true
    (BT.Move ev) -> newParentId ev /= oldParentId ev
    _ -> false

-- | This function listens to blockly events and debounces the event listener so that the resulting
-- | Aff is completed after `time` milliseconds without events.
-- | NOTE: The part of this code that depends on blockly is rather minimal (addChangeListener workspace and
-- |       removeChangeListener workspace). We don't care about the contents of the event, just the fact that
-- |       it is fired, so we can debounce it.
-- |       If we need a debounce functionality later on, see if it makes sense to refactor this. I didn't do it
-- |       for the PR that introduced this code as it's not clear at the moment wether the debounce should be
-- |       tied to event listeners or if we can do it with plain Aff's
waitForEvents :: Workspace -> Int -> Aff Unit
waitForEvents workspace time = liftEffect (Ref.new Nothing) >>= waitForEventsAndCleanResources
  where
  -- Make sure that the event listener is removed no matter what
  waitForEventsAndCleanResources :: Ref (Maybe EventListener) -> Aff Unit
  waitForEventsAndCleanResources listenerRef =
    finally
      (liftEffect $ removeListener listenerRef)
      (waitForEvent listenerRef)

  waitForEvent :: Ref (Maybe EventListener) -> Aff Unit
  waitForEvent listenerRef = makeAff resolver
    where
    resolver cb = do
      -- The timerRef is a mutable reference to the timeoutId so we can
      -- cancel the "debounce" timer every time there is a new event.
      timerRef <- Ref.new Nothing
      let
        -- Helper fn that creates the timer that resolves the Aff if there
        -- is no event in `time` milliseconds
        resolveAfterTimeout = do
          timeoutId <- setTimeout time $ cb $ Right unit
          Ref.write (Just timeoutId) timerRef
      -- Create the initial timer
      resolveAfterTimeout
      -- Create and subscribe the event listener
      listener <-
        eventListener \event -> do
          -- Clear the previous timer and and fire a new one
          mTimeoutId <- Ref.read timerRef
          for_ mTimeoutId clearTimeout
          resolveAfterTimeout
      Ref.write (Just listener) listenerRef
      addChangeListener workspace listener
      -- We can return a nonCanceler because the cleanup is done in the finally
      pure nonCanceler

  removeListener :: Ref (Maybe EventListener) -> Effect Unit
  removeListener listenerRef = do
    mListener <- Ref.read listenerRef
    for_ mListener \listener ->
      removeChangeListener workspace listener

-- Runs an effectful action temporarily disabling the blockly events, waiting
-- `time` milliseconds for those events to settle, and then re-subscribe.
runWithoutEventSubscription ::
  forall m state action message slots.
  MonadAff m =>
  Int ->
  (BlocklyEvent -> action) ->
  Effect Unit ->
  HalogenM { blocklyState :: Maybe BlocklyState, blocklyEventSubscription :: Maybe SubscriptionId | state } action slots message m Unit
runWithoutEventSubscription time toAction doEffect = do
  let
    _blocklyEventSubscription = prop (SProxy :: SProxy "blocklyEventSubscription")

    _blocklyState = prop (SProxy :: SProxy "blocklyState")
  mSubscription <- use _blocklyEventSubscription
  mBlocklyState <- use _blocklyState
  for_ mBlocklyState \{ workspace } -> do
    -- Unsubscribe from blockly events
    for_ mSubscription H.unsubscribe
    -- Do the efectful computation that will trigger events we want to skip
    liftEffect doEffect
    liftAff $ waitForEvents workspace time
    -- Resubscribe to blockly events
    newSubscription <- H.subscribe $ blocklyEvents toAction workspace
    assign _blocklyEventSubscription (Just newSubscription)
