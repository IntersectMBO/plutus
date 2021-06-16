module Template.Types
  ( State
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Data.BigInteger (BigInteger)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import InputField.Types (Action, State) as InputField
import Marlowe.Template (TemplateContent)
import Marlowe.Extended.Metadata (ContractTemplate)
import Marlowe.Semantics (TokenName)
import Template.Validation (RoleError)
import WalletData.Types (WalletLibrary)

type State
  = { template :: ContractTemplate
    , contractNickname :: String
    , roleWalletInputs :: Map TokenName (InputField.State RoleError)
    , templateContent :: TemplateContent
    , slotContentStrings :: Map String String
    }

data Action
  = SetTemplate ContractTemplate
  | OpenTemplateLibraryCard
  | OpenCreateWalletCard TokenName
  | OpenSetupConfirmationCard
  | CloseSetupConfirmationCard
  | SetContractNickname String
  | UpdateRoleWalletValidators WalletLibrary
  | RoleWalletInputAction TokenName (InputField.Action RoleError)
  | SetSlotContent String String -- slot input comes from the HTML as a dateTimeString
  | SetValueContent String (Maybe BigInteger)
  | StartContract

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (SetTemplate _) = Just $ defaultEvent "SetTemplate"
  toEvent OpenTemplateLibraryCard = Nothing
  toEvent (OpenCreateWalletCard tokenName) = Nothing
  toEvent OpenSetupConfirmationCard = Nothing
  toEvent CloseSetupConfirmationCard = Nothing
  toEvent (SetContractNickname _) = Just $ defaultEvent "SetContractNickname"
  toEvent (UpdateRoleWalletValidators _) = Nothing
  toEvent (RoleWalletInputAction _ inputFieldAction) = toEvent inputFieldAction
  toEvent (SetSlotContent _ _) = Just $ defaultEvent "SetSlotContent"
  toEvent (SetValueContent _ _) = Just $ defaultEvent "SetValueContent"
  toEvent StartContract = Just $ defaultEvent "StartContract"
