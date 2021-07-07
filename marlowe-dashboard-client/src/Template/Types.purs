module Template.Types
  ( State
  , ContractSetupStage(..)
  , Input
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import InputField.Types (Action, State) as InputField
import Marlowe.Extended.Metadata (ContractTemplate)
import Marlowe.Semantics (Slot, TokenName)
import Template.Validation (ContractNicknameError, RoleError, SlotError, ValueError)
import WalletData.Types (WalletLibrary)

type State
  = { contractSetupStage :: ContractSetupStage
    , contractTemplate :: ContractTemplate
    , contractNicknameInput :: InputField.State ContractNicknameError
    , roleWalletInputs :: Map TokenName (InputField.State RoleError)
    , slotContentInputs :: Map String (InputField.State SlotError)
    , valueContentInputs :: Map String (InputField.State ValueError)
    }

data ContractSetupStage
  = Start
  | Overview
  | Setup
  | Review

type Input
  = { currentSlot :: Slot
    , walletLibrary :: WalletLibrary
    }

data Action
  = SetContractSetupStage ContractSetupStage
  | SetTemplate ContractTemplate
  | OpenCreateWalletCard TokenName
  | ContractNicknameInputAction (InputField.Action ContractNicknameError)
  | UpdateRoleWalletValidators
  | UpdateSlotContentValidators
  | RoleWalletInputAction TokenName (InputField.Action RoleError)
  | SlotContentInputAction String (InputField.Action SlotError)
  | ValueContentInputAction String (InputField.Action ValueError)
  | StartContract

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (SetContractSetupStage _) = Just $ defaultEvent "SetContractSetupStage"
  toEvent (SetTemplate _) = Just $ defaultEvent "SetTemplate"
  toEvent (OpenCreateWalletCard tokenName) = Nothing
  toEvent (ContractNicknameInputAction inputFieldAction) = toEvent inputFieldAction
  toEvent UpdateRoleWalletValidators = Nothing
  toEvent UpdateSlotContentValidators = Nothing
  toEvent (RoleWalletInputAction _ inputFieldAction) = toEvent inputFieldAction
  toEvent (SlotContentInputAction _ inputFieldAction) = toEvent inputFieldAction
  toEvent (ValueContentInputAction _ inputFieldAction) = toEvent inputFieldAction
  toEvent StartContract = Just $ defaultEvent "StartContract"
