module Dashboard.Lenses
  ( _contactsState
  , _walletDetails
  , _walletCompanionStatus
  , _menuOpen
  , _card
  , _cardOpen
  , _contracts
  , _contract
  , _contractFilter
  , _selectedContractFollowerAppId
  , _selectedContract
  , _templateState
  ) where

import Prologue
import Contract.Types (State) as Contract
import Dashboard.Types (Card, ContractFilter, State, WalletCompanionStatus)
import Data.Lens (Lens', Traversal', set, wander)
import Data.Lens.At (at)
import Data.Lens.Prism.Maybe (_Just)
import Data.Lens.Record (prop)
import Data.Map (Map, insert, lookup)
import Data.Symbol (SProxy(..))
import Marlowe.PAB (PlutusAppId)
import Template.Types (State) as Template
import Contacts.Types (State) as Contacts
import Contacts.Types (WalletDetails)

_contactsState :: Lens' State Contacts.State
_contactsState = prop (SProxy :: SProxy "contactsState")

_walletDetails :: Lens' State WalletDetails
_walletDetails = prop (SProxy :: SProxy "walletDetails")

_walletCompanionStatus :: Lens' State WalletCompanionStatus
_walletCompanionStatus = prop (SProxy :: SProxy "walletCompanionStatus")

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

_templateState :: Lens' State Template.State
_templateState = prop (SProxy :: SProxy "templateState")
