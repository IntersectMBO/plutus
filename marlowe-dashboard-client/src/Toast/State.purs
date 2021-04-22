module Toast.State
  ( defaultState
  , handleAction
  ) where

import Prelude
import Data.Foldable (for_)
import Data.Lens (assign)
import Data.Lens.Extra (peruse)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Effect.Aff (error)
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, RefLabel(..), getHTMLElementRef, subscribe, unsubscribe)
import Halogen.Animation (animateAndWaitUntilFinish)
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
        EventSource.close emitter
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
  mElement <- getHTMLElementRef (RefLabel "collapsed-toast")
  for_ mElement $ subscribe <<< animateAndWaitUntilFinish "to-bottom" CloseToast
