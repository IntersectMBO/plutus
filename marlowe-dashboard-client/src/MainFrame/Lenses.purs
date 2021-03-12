module MainFrame.Lenses
  ( _wallets
  , _newWalletNickname
  , _newWalletContractId
  , _remoteDataPubKey
  , _templates
  , _subState
  , _webSocketStatus
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
import Marlowe.Semantics (PubKey)
import Network.RemoteData (RemoteData)
import Pickup.Types (State) as Pickup
import Play.Types (State) as Play
import Servant.PureScript.Ajax (AjaxError)
import WalletData.Types (Nickname, WalletLibrary)

_wallets :: Lens' State WalletLibrary
_wallets = prop (SProxy :: SProxy "wallets")

_newWalletNickname :: Lens' State Nickname
_newWalletNickname = prop (SProxy :: SProxy "newWalletNickname")

_newWalletContractId :: Lens' State String
_newWalletContractId = prop (SProxy :: SProxy "newWalletContractId")

_remoteDataPubKey :: Lens' State (RemoteData AjaxError PubKey)
_remoteDataPubKey = prop (SProxy :: SProxy "remoteDataPubKey")

_templates :: Lens' State (Array ContractTemplate)
_templates = prop (SProxy :: SProxy "templates")

_subState :: Lens' State (Either Pickup.State Play.State)
_subState = prop (SProxy :: SProxy "subState")

_webSocketStatus :: Lens' State WebSocketStatus
_webSocketStatus = prop (SProxy :: SProxy "webSocketStatus")

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
