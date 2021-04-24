module MainFrame.Lenses
  ( _webSocketStatus
  , _subState
  , _toast
  , _pickupState
  , _playState
  ) where

import Prelude
import Data.Either (Either)
import Data.Lens (Lens', Traversal')
import Data.Lens.Prism.Either (_Left, _Right)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import MainFrame.Types (State, WebSocketStatus)
import Pickup.Types (State) as Pickup
import Play.Types (State) as Play
import Toast.Types (State) as Toast

_webSocketStatus :: Lens' State WebSocketStatus
_webSocketStatus = prop (SProxy :: SProxy "webSocketStatus")

_subState :: Lens' State (Either Pickup.State Play.State)
_subState = prop (SProxy :: SProxy "subState")

_toast :: Lens' State Toast.State
_toast = prop (SProxy :: SProxy "toast")

------------------------------------------------------------
_pickupState :: Traversal' State Pickup.State
_pickupState = _subState <<< _Left

_playState :: Traversal' State Play.State
_playState = _subState <<< _Right
