module Toast.Lenses
  ( _mToast
  , _toastMessage
  , _expanded
  , _timeoutSubscription
  ) where

import Prelude
import Data.Lens (Lens', _Just)
import Data.Lens.Record (prop)
import Data.Lens.Traversal (Traversal')
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Halogen (SubscriptionId)
import Toast.Types (State, ToastMessage, ToastState)

-- TODO: when we upgrade to 0.14 change this to AffineTraversal
_mToast :: Lens' State (Maybe ToastState)
_mToast = prop (SProxy :: SProxy "mToast")

_toastMessage :: Traversal' State ToastMessage
_toastMessage = _mToast <<< _Just <<< prop (SProxy :: SProxy "message")

_expanded :: Traversal' State Boolean
_expanded = prop (SProxy :: SProxy "mToast") <<< _Just <<< prop (SProxy :: SProxy "expanded")

_timeoutSubscription :: Traversal' State SubscriptionId
_timeoutSubscription = prop (SProxy :: SProxy "mToast") <<< _Just <<< prop (SProxy :: SProxy "timeoutSubscription")
