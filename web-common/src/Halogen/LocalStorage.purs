module Halogen.LocalStorage (localStorageEvents) where

import Prelude
import Control.Coroutine (connect, consumer, runProcess)
import Data.Maybe (Maybe(..))
import Effect.Aff (forkAff, killFiber)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (error)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import LocalStorage (RawStorageEvent)
import LocalStorage as LocalStorage

-- This EventSource allows you to subscribe to local storage events from within
-- a Halogen handle action, and dispatch custom actions using the `toAction` wrapper.
localStorageEvents ::
  forall m action.
  MonadAff m =>
  (RawStorageEvent -> action) ->
  EventSource m action
localStorageEvents toAction =
  EventSource.affEventSource \emitter -> do
    fiber <-
      forkAff $ runProcess $ connect LocalStorage.listen
        $ consumer \event -> do
            EventSource.emit emitter (toAction event)
            pure Nothing
    pure
      $ EventSource.Finalizer
      $ killFiber (error "unsubscribing") fiber
