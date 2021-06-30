module Hint.State (component, hint) where

import Prelude
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Data.Array (all)
import Data.Foldable (for_)
import Data.Int (toNumber)
import Data.Lens (assign, set, use)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Data.Traversable (for, traverse)
import Effect.Aff.Class (class MonadAff)
import Halogen (Component, HalogenM, Slot, get, getHTMLElementRef, liftEffect, mkComponent, modify_)
import Halogen as H
import Halogen.HTML (ComponentHTML, HTML, PlainHTML, slot)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import Hint.Lenses (_active, _content, _mGlobalClickSubscription, _mPopperInstance, _placement)
import Hint.Types (Action(..), Input, State, arrowRef, hintRef, popoutRef)
import Hint.View (render)
import Popper (OffsetOption(..), PaddingOption(..), Placement, PositioningStrategy(..), arrow, createPopper, defaultFlip, defaultModifiers, defaultPreventOverflow, destroyPopper, flipPlacement, forceUpdate, offset, pAll, preventOverflow)
import Web.Event.Event (EventType(..))
import Web.Event.EventTarget (addEventListener, eventListener, removeEventListener)
import Web.HTML (HTMLElement, window)
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.HTMLElement (DOMRect, getBoundingClientRect)
import Web.HTML.Window (document)
import Web.UIEvent.MouseEvent as MouseEvent

_hintSlot :: SProxy "hintSlot"
_hintSlot = SProxy

hint ::
  forall slots m action.
  MonadAff m =>
  Array String ->
  String ->
  Placement ->
  PlainHTML ->
  ComponentHTML action ( hintSlot :: forall query. Slot query Void String | slots ) m
hint hintElementClasses ref placement content =
  slot
    _hintSlot
    ref
    component
    { content, placement, hintElementClasses }
    absurd

initialState :: Input -> State
initialState { content, placement, hintElementClasses } =
  { content
  , placement
  , hintElementClasses
  , active: false
  , mPopperInstance: Nothing
  , mGlobalClickSubscription: Nothing
  }

component ::
  forall m query.
  MonadAff m =>
  Component HTML query Input Void m
component =
  mkComponent
    { initialState
    , render
    , eval:
        H.mkEval
          $ H.defaultEval
              { initialize = Just Init
              , finalize = Just Finalize
              , handleAction = handleAction
              , receive = \input -> Just $ OnNewInput input
              }
    }

handleAction ::
  forall m slots.
  MonadAff m =>
  Action ->
  HalogenM State Action slots Void m Unit
handleAction Init = do
  placement <- use _placement
  mPopperInstance <-
    runMaybeT do
      arrowElem <- MaybeT $ getHTMLElementRef arrowRef
      let
        modifiers =
          defaultModifiers
            <> [ arrow arrowElem (PaddingValue $ pAll 0.0)
              , offset (OffsetValue { skidding: 0.0, distance: 8.0 })
              , preventOverflow defaultPreventOverflow
              , flipPlacement defaultFlip
              ]
      hintElem <- MaybeT $ getHTMLElementRef hintRef
      popoutElem <- MaybeT $ getHTMLElementRef popoutRef
      liftEffect $ createPopper hintElem popoutElem { placement, modifiers, strategy: Fixed }
  assign _mPopperInstance mPopperInstance

handleAction Finalize = do
  mPopperInstance <- use _mPopperInstance
  for_ mPopperInstance $ liftEffect <<< destroyPopper

handleAction (OnNewInput input) = do
  { active, content, placement } <- get
  modify_
    ( set _content input.content
        <<< set _placement input.placement
    )
  when active forceUpdatePopper

handleAction Open = do
  mHintElem <- getHTMLElementRef hintRef
  mPopoutElem <- getHTMLElementRef popoutRef
  let
    mElements :: Maybe (Array HTMLElement)
    mElements = (\a b -> [ a, b ]) <$> mHintElem <*> mPopoutElem
  mGlobalClickSubscription <- traverse (H.subscribe <<< clickOutsideEventSource) mElements
  modify_
    ( set _active true
        <<< set _mGlobalClickSubscription mGlobalClickSubscription
    )
  forceUpdatePopper

handleAction Close = do
  mGlobalClickSubscription <- use _mGlobalClickSubscription
  for_ mGlobalClickSubscription H.unsubscribe
  modify_
    ( set _active false
        <<< set _mGlobalClickSubscription Nothing
    )

handleAction Toggle = do
  active <- use _active
  if active then
    handleAction Close
  else
    handleAction Open

type Point2D
  = { x :: Number, y :: Number }

outside :: DOMRect -> Point2D -> Boolean
outside { top, bottom, left, right } { x, y } = x < left || x > right || y > bottom || y < top

inside :: DOMRect -> Point2D -> Boolean
inside rect = not <<< outside rect

-- This subscription attaches to the document's click event and checks wether a click was
-- made outside the hint dialog and the hint element. We need to check for both elements
-- because we also receive the event that starts this subscription, which is inside the hint
-- element but outside the hint dialog.
-- Initially this was done using `eventListenerEventSource` which is simpler than `effectEventSource`
-- (as you don't need to manually add and remove the event listener)
-- but it had a problem of not being able to perform effects, so we couldn't recalculate
-- the client rect on each click.
clickOutsideEventSource ::
  forall m.
  MonadAff m =>
  Array HTMLElement ->
  EventSource m Action
clickOutsideEventSource elements =
  EventSource.effectEventSource \emitter -> do
    listener <-
      eventListener \evt -> do
        -- We recalculate the client rect for each element because Popper might move them
        clientRects <- for elements getBoundingClientRect
        let
          mClickOutside =
            MouseEvent.fromEvent evt
              <#> \mouseEvent ->
                  let
                    point =
                      { x: toNumber $ MouseEvent.clientX mouseEvent
                      , y: toNumber $ MouseEvent.clientY mouseEvent
                      }
                  in
                    all (\rect -> outside rect point) clientRects
        when (mClickOutside == Just true) $ EventSource.emit emitter Close
    -- Add the event listener and remove it once the subscription finalizes
    docTarget <- liftEffect $ map HTMLDocument.toEventTarget $ document =<< window
    addEventListener (EventType "click") listener false docTarget
    pure $ EventSource.Finalizer $ removeEventListener (EventType "click") listener false docTarget

forceUpdatePopper :: forall m slots. MonadAff m => HalogenM State Action slots Void m Unit
forceUpdatePopper = do
  mPopperInstance <- use _mPopperInstance
  for_ mPopperInstance $ liftEffect <<< forceUpdate
