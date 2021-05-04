module Play.Lenses
  ( _walletLibrary
  , _walletDetails
  , _menuOpen
  , _screen
  , _cards
  , _newWalletNickname
  , _newWalletCompanionAppIdString
  , _newWalletInfo
  , _currentSlot
  , _templateState
  , _contractsState
  , _allContracts
  , _selectedContract
  ) where

import Prelude
import Contract.Types (State) as Contract
import ContractHome.Lenses (_contracts, _selectedContract) as ContractHome
import ContractHome.Types (State) as ContractHome
import Data.Lens (Lens', Traversal')
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Symbol (SProxy(..))
import Marlowe.PAB (PlutusAppId)
import Marlowe.Semantics (Slot)
import Play.Types (Card, Screen, State)
import Template.Types (State) as Template
import Types (WebData)
import WalletData.Types (WalletDetails, WalletInfo, WalletLibrary, WalletNickname)

_walletLibrary :: Lens' State WalletLibrary
_walletLibrary = prop (SProxy :: SProxy "walletLibrary")

_walletDetails :: Lens' State WalletDetails
_walletDetails = prop (SProxy :: SProxy "walletDetails")

_menuOpen :: Lens' State Boolean
_menuOpen = prop (SProxy :: SProxy "menuOpen")

_screen :: Lens' State Screen
_screen = prop (SProxy :: SProxy "screen")

_cards :: Lens' State (Array Card)
_cards = prop (SProxy :: SProxy "cards")

_newWalletNickname :: Lens' State WalletNickname
_newWalletNickname = prop (SProxy :: SProxy "newWalletNickname")

_newWalletCompanionAppIdString :: Lens' State String
_newWalletCompanionAppIdString = prop (SProxy :: SProxy "newWalletCompanionAppIdString")

_newWalletInfo :: Lens' State (WebData WalletInfo)
_newWalletInfo = prop (SProxy :: SProxy "newWalletInfo")

_currentSlot :: Lens' State Slot
_currentSlot = prop (SProxy :: SProxy "currentSlot")

_templateState :: Lens' State Template.State
_templateState = prop (SProxy :: SProxy "templateState")

_contractsState :: Lens' State ContractHome.State
_contractsState = prop (SProxy :: SProxy "contractsState")

_allContracts :: Lens' State (Map PlutusAppId Contract.State)
_allContracts = _contractsState <<< ContractHome._contracts

-- This traversal focus on a specific contract indexed by another property of the state
_selectedContract :: Traversal' State Contract.State
_selectedContract = _contractsState <<< ContractHome._selectedContract
