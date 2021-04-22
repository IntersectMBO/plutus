module MainFrame.Lenses
  ( _wallets
  , _newWalletDetails
  , _templates
  , _subState
  , _webSocketStatus
  , _toast
  , _pickupState
  , _playState
  , _screen
  , _card
  ) where

import Prelude
import Data.Either (Either)
import Data.Lens (Lens', Traversal')
import Data.Lens.Prism.Either (_Left, _Right)
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import MainFrame.Types (State, WebSocketStatus)
import Marlowe.Extended.Template (ContractTemplate)
import Pickup.Types (State) as Pickup
import Play.Types (State) as Play
import Toast.Types (State) as Toast
import WalletData.Types (WalletLibrary, NewWalletDetails)

_wallets :: Lens' State WalletLibrary
_wallets = prop (SProxy :: SProxy "wallets")

_newWalletDetails :: Lens' State NewWalletDetails
_newWalletDetails = prop (SProxy :: SProxy "newWalletDetails")

_templates :: Lens' State (Array ContractTemplate)
_templates = prop (SProxy :: SProxy "templates")

_subState :: Lens' State (Either Pickup.State Play.State)
_subState = prop (SProxy :: SProxy "subState")

_webSocketStatus :: Lens' State WebSocketStatus
_webSocketStatus = prop (SProxy :: SProxy "webSocketStatus")

_toast :: Lens' State Toast.State
_toast = prop (SProxy :: SProxy "toast")

------------------------------------------------------------
_pickupState :: Traversal' State Pickup.State
_pickupState = _subState <<< _Left

_playState :: Traversal' State Play.State
_playState = _subState <<< _Right

------------------------------------------------------------
_screen :: forall s b. Lens' { screen :: s | b } s
_screen = prop (SProxy :: SProxy "screen")

_card :: forall c b. Lens' { card :: c | b } c
_card = prop (SProxy :: SProxy "card")
