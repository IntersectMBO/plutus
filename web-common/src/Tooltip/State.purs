module Tooltip.State (component, tooltip) where

import Prelude
import Control.Bind (bindFlipped)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Data.Foldable (for_)
import Data.Lens (assign, set, use)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Halogen (Component, HalogenM, Slot, get, getHTMLElementRef, liftEffect, mkComponent, modify_)
import Halogen as H
import Halogen.HTML (ComponentHTML, HTML, slot)
import Halogen.Query.EventSource (eventListenerEventSource)
import Popper (OffsetOption(..), PaddingOption(..), Placement, PositioningStrategy(..), arrow, createPopper, defaultModifiers, defaultPreventOverflow, destroyPopper, forceUpdate, offset, pAll, preventOverflow)
import Tooltip.Lenses (_active, _mPopperInstance, _message, _placement)
import Tooltip.Types (Action(..), Input, RefferenceId(..), State, arrowRef, tooltipRef)
import Tooltip.View (render)
import Web.DOM.NonElementParentNode (getElementById)
import Web.Event.Event (EventType(..))
import Web.HTML (HTMLElement, window)
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window (document)

_tooltipSlot :: SProxy "tooltipSlot"
_tooltipSlot = SProxy

tooltip ::
  forall slots m action.
  MonadAff m =>
  String ->
  RefferenceId ->
  Placement ->
  ComponentHTML action ( tooltipSlot :: forall query. Slot query Void RefferenceId | slots ) m
tooltip message reference placement = slot _tooltipSlot reference component { message, reference, placement } absurd

initialState :: Input -> State
initialState { message, reference, placement } =
  { message
  , reference
  , placement
  , active: false
  , mPopperInstance: Nothing
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

-- We need to use id and not RefLabel because the RefLabel don't cross component boundaries.
getElementById' :: String -> Effect (Maybe HTMLElement)
getElementById' id = map (bindFlipped HTMLElement.fromElement) $ getElementById id <=< map toNonElementParentNode $ document =<< window

handleAction ::
  forall m slots.
  MonadAff m =>
  Action ->
  HalogenM State Action slots Void m Unit
handleAction Init = do
  ({ placement, reference: RefId refId }) <- get
  mPopperInstance <-
    runMaybeT do
      arrowElem <- MaybeT $ getHTMLElementRef arrowRef
      let
        modifiers =
          defaultModifiers
            <> [ arrow arrowElem (PaddingValue $ pAll 0.0)
              , offset (OffsetValue { skidding: 0.0, distance: 8.0 })
              , preventOverflow defaultPreventOverflow
              ]
      refElem <- MaybeT $ liftEffect $ getElementById' refId
      tooltipElem <- MaybeT $ getHTMLElementRef tooltipRef
      popperInstance <- liftEffect $ createPopper refElem tooltipElem { placement, modifiers, strategy: Absolute }
      -- We add event listeners to the target element to know when to show and hide the tooltip. We don't store the
      -- subscriptionId to manually remove it because we are inside a component (not a subcomponent), so any
      -- subscriptions will be terminated when the component is no longer rendered.
      -- TODO: We could later implement the performance suggestions from https://popper.js.org/docs/v2/tutorial/#performance
      void $ MaybeT $ map pure $ H.subscribe $ eventListenerEventSource (EventType "mouseenter") (HTMLElement.toEventTarget refElem) (const $ Just Show)
      void $ MaybeT $ map pure $ H.subscribe $ eventListenerEventSource (EventType "focus") (HTMLElement.toEventTarget refElem) (const $ Just Show)
      void $ MaybeT $ map pure $ H.subscribe $ eventListenerEventSource (EventType "mouseleave") (HTMLElement.toEventTarget refElem) (const $ Just Hide)
      void $ MaybeT $ map pure $ H.subscribe $ eventListenerEventSource (EventType "blur") (HTMLElement.toEventTarget refElem) (const $ Just Hide)
      pure popperInstance
  assign _mPopperInstance mPopperInstance

handleAction Finalize = do
  mPopperInstance <- use _mPopperInstance
  for_ mPopperInstance $ liftEffect <<< destroyPopper

-- TODO: This is being called 5 times per second per active tooltip. There is probably an overhead in the timer from the PAB
-- that causes 5 re-renders per second, but also we should investigate on memoize this
handleAction (OnNewInput input) = do
  { active, message, placement } <- get
  when (message /= input.message || placement /= input.placement)
    $ modify_
        ( set _message input.message
            <<< set _placement input.placement
        )
  when active forceUpdatePopper

handleAction Show = do
  assign _active true
  forceUpdatePopper

handleAction Hide = assign _active false

forceUpdatePopper :: forall m slots. MonadAff m => HalogenM State Action slots Void m Unit
forceUpdatePopper = do
  mPopperInstance <- use _mPopperInstance
  for_ mPopperInstance $ liftEffect <<< forceUpdate
