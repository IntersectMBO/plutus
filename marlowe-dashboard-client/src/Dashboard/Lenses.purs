module Dashboard.Lenses
  ( _walletLibrary
  , _walletDetails
  , _menuOpen
  , _card
  , _cardOpen
  , _contracts
  , _contract
  , _contractFilter
  , _selectedContractFollowerAppId
  , _selectedContract
  , _walletNicknameInput
  , _walletIdInput
  , _remoteWalletInfo
  , _templateState
  ) where

import Prelude
import Contract.Types (State) as Contract
import Dashboard.Types (Card, ContractFilter, State)
import Data.Lens (Lens', Traversal', set, wander)
import Data.Lens.At (at)
import Data.Lens.Prism.Maybe (_Just)
import Data.Lens.Record (prop)
import Data.Map (Map, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import InputField.Types (State) as InputField
import Marlowe.PAB (PlutusAppId)
import Template.Types (State) as Template
import Types (WebData)
import WalletData.Types (WalletDetails, WalletInfo, WalletLibrary)
import WalletData.Validation (WalletIdError, WalletNicknameError)

_walletLibrary :: Lens' State WalletLibrary
_walletLibrary = prop (SProxy :: SProxy "walletLibrary")

_walletDetails :: Lens' State WalletDetails
_walletDetails = prop (SProxy :: SProxy "walletDetails")

_menuOpen :: Lens' State Boolean
_menuOpen = prop (SProxy :: SProxy "menuOpen")

_card :: Lens' State (Maybe Card)
_card = prop (SProxy :: SProxy "card")

_cardOpen :: Lens' State Boolean
_cardOpen = prop (SProxy :: SProxy "cardOpen")

_contracts :: Lens' State (Map PlutusAppId Contract.State)
_contracts = prop (SProxy :: SProxy "contracts")

_contract :: PlutusAppId -> Traversal' State Contract.State
_contract followerAppId = _contracts <<< at followerAppId <<< _Just

_contractFilter :: Lens' State ContractFilter
_contractFilter = prop (SProxy :: SProxy "contractFilter")

_selectedContractFollowerAppId :: Lens' State (Maybe PlutusAppId)
_selectedContractFollowerAppId = prop (SProxy :: SProxy "selectedContractFollowerAppId")

-- This traversal focus on a specific contract indexed by another property of the state
_selectedContract :: Traversal' State Contract.State
_selectedContract =
  wander \f state -> case state.selectedContractFollowerAppId of
    Just ix
      | Just contract <- lookup ix state.contracts ->
        let
          updateContract contract' = insert ix contract' state.contracts
        in
          (\contract' -> set _contracts (updateContract contract') state) <$> f contract
    _ -> pure state

_walletNicknameInput :: Lens' State (InputField.State WalletNicknameError)
_walletNicknameInput = prop (SProxy :: SProxy "walletNicknameInput")

_walletIdInput :: Lens' State (InputField.State WalletIdError)
_walletIdInput = prop (SProxy :: SProxy "walletIdInput")

_remoteWalletInfo :: Lens' State (WebData WalletInfo)
_remoteWalletInfo = prop (SProxy :: SProxy "remoteWalletInfo")

_templateState :: Lens' State Template.State
_templateState = prop (SProxy :: SProxy "templateState")
