module MainFrame.Lenses
  ( _webSocketStatus
  , _currentSlot
  , _subState
  , _toast
  , _welcomeState
  , _dashboardState
  ) where

import Prelude
import Dashboard.Types (State) as Dashboard
import Data.Either (Either)
import Data.Lens (Lens', Traversal')
import Data.Lens.Prism.Either (_Left, _Right)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import MainFrame.Types (State, WebSocketStatus)
import Marlowe.Semantics (Slot)
import Toast.Types (State) as Toast
import Welcome.Types (State) as Welcome

_webSocketStatus :: Lens' State WebSocketStatus
_webSocketStatus = prop (SProxy :: SProxy "webSocketStatus")

_currentSlot :: Lens' State Slot
_currentSlot = prop (SProxy :: SProxy "currentSlot")

_subState :: Lens' State (Either Welcome.State Dashboard.State)
_subState = prop (SProxy :: SProxy "subState")

_toast :: Lens' State Toast.State
_toast = prop (SProxy :: SProxy "toast")

------------------------------------------------------------
_welcomeState :: Traversal' State Welcome.State
_welcomeState = _subState <<< _Left

_dashboardState :: Traversal' State Dashboard.State
_dashboardState = _subState <<< _Right
