module Toast.State
  ( defaultState
  , handleAction
  ) where

import Prelude
import Data.Lens (assign, set, use)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Effect.Aff (error)
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, modify_, subscribe)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import Toast.Lenses (_expanded, _mToast)
import Toast.Types (Action(..), State, Toast)

defaultState :: State
defaultState =
  { mToast: Nothing
  , expanded: false
  }

toastTimeoutSubscription ::
  forall m.
  MonadAff m =>
  Toast ->
  EventSource m Action
toastTimeoutSubscription toast =
  EventSource.affEventSource \emitter -> do
    fiber <-
      Aff.forkAff do
        Aff.delay $ Milliseconds toast.timeout
        EventSource.emit emitter ToastTimeout
    pure $ EventSource.Finalizer $ Aff.killFiber (error "removing aff") fiber

handleAction ::
  forall m slots msg.
  MonadAff m =>
  Action ->
  HalogenM State Action slots msg m Unit
handleAction (AddToast toast) = do
  void $ subscribe $ toastTimeoutSubscription toast
  modify_
    $ set _expanded false
    <<< set _mToast (Just toast)

handleAction ExpandToast = assign _expanded true

handleAction CloseToast =
  modify_
    $ set _expanded false
    <<< set _mToast Nothing

handleAction ToastTimeout = do
  expanded <- use _expanded
  when (not expanded) $ handleAction CloseToast
