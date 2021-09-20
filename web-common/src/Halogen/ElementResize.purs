module Halogen.ElementResize where

import Prelude
import Data.Array (head)
import Data.Foldable (for_)
import Effect.Aff.Class (class MonadAff)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import Web.DOM (Element)
import Web.DOM.ResizeObserver (ResizeObserverBoxOptions, ResizeObserverEntry, observe, resizeObserver, unobserve)

elementResize ::
  forall m action.
  MonadAff m =>
  ResizeObserverBoxOptions ->
  (ResizeObserverEntry -> action) ->
  Element ->
  EventSource m action
elementResize options toAction element =
  EventSource.effectEventSource \emitter -> do
    observer <-
      resizeObserver \entries _ ->
        for_ (head entries) \entry -> EventSource.emit emitter (toAction entry)
    observe element options observer
    pure $ EventSource.Finalizer $ unobserve element observer
