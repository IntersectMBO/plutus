module Toast.State
  ( defaultState
  , handleAction
  ) where

import Prelude
import Data.Foldable (for_)
import Data.Lens (assign, preview)
import Data.Lens.Extra (peruse)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Time.Duration (Milliseconds(..))
import Effect.Aff (error)
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, get, subscribe, unsubscribe)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import Toast.Lenses (_expanded, _mToast, _timeoutSubscription)
import Toast.Types (Action(..), State, ToastMessage)

defaultState :: State
defaultState =
  { mToast: Nothing
  }

toastTimeoutSubscription ::
  forall m.
  MonadAff m =>
  ToastMessage ->
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
  timeoutSubscription <- subscribe $ toastTimeoutSubscription toast
  assign _mToast (Just { message: toast, expanded: false, timeoutSubscription })

handleAction ExpandToast = do
  mSubscriptionId <- peruse _timeoutSubscription
  assign _expanded true
  for_ mSubscriptionId unsubscribe

handleAction CloseToast = assign _mToast Nothing

handleAction ToastTimeout = do
  state <- get
  let
    expanded = fromMaybe false $ preview _expanded state

    mSubscriptionId = preview _timeoutSubscription state
  for_ mSubscriptionId unsubscribe
  when (not expanded) $ handleAction CloseToast
