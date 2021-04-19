module Template.Types
  ( State
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.BigInteger (BigInteger)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Marlowe.Extended (TemplateContent)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Semantics (TokenName)
import WalletData.Types (WalletNickname)

type State
  = { template :: ContractTemplate
    , contractNickname :: String
    , roleWallets :: Map TokenName WalletNickname
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
  | SetRoleWallet TokenName WalletNickname
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
  toEvent (SetRoleWallet _ _) = Just $ defaultEvent "SetRoleWallet"
  toEvent (SetSlotContent _ _) = Just $ defaultEvent "SetSlotContent"
  toEvent (SetValueContent _ _) = Just $ defaultEvent "SetValueContent"
  toEvent StartContract = Just $ defaultEvent "StartContract"
