module Halogen.ElementVisible where

import Prelude
import Data.Array (head)
import Data.Foldable (for_)
import Effect.Aff.Class (class MonadAff)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import Web.DOM (Element)
import Web.DOM.IntersectionObserver (intersectionObserver, observe, unobserve)

-- This Halogen EventSource uses the IntersectionObserver to detect if an element is visible in the
-- viewport.
-- The `toAction` callback allows the subscriber to dispatch a particular action when the element is
-- visible or not.
elementVisible ::
  forall m action.
  MonadAff m =>
  (Boolean -> action) ->
  Element ->
  EventSource m action
elementVisible toAction element =
  EventSource.effectEventSource \emitter -> do
    observer <-
      intersectionObserver \entries _ ->
        for_ (head entries) \entry -> EventSource.emit emitter (toAction entry.isIntersecting)
    observe element {} observer
    pure $ EventSource.Finalizer $ unobserve element observer
