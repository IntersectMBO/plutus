module Template.Types
  ( module ExtendedREs
  , State
  , Template
  , Screen(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.BigInteger (BigInteger)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Marlowe.Extended (Contract, IntegerTemplateType, MetaData, TemplateContent, ContractTemplate)
import Marlowe.Extended (MetaData) as ExtendedREs
import Marlowe.Semantics (TokenName)

type Template
  = ContractTemplate

type State
  = { template :: Template
    , contractNickname :: String
    , roleWallets :: Map String String
    , templateContent :: TemplateContent
    }

data Screen
  = ContractRolesScreen
  | ContractParametersScreen
  | ContractReviewScreen

derive instance eqScreen :: Eq Screen

data Action
  = SetTemplate Template
  | SetScreen Screen
  | ToggleTemplateLibraryCard
  | ToggleSetupConfirmationCard
  | SetContractNickname String
  | SetRoleWallet String String
  | SetParameter IntegerTemplateType String (Maybe BigInteger)
  | StartContract

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (SetTemplate _) = Just $ defaultEvent "SetTemplate"
  toEvent (SetScreen _) = Just $ defaultEvent "SetTemplateScreen"
  toEvent ToggleTemplateLibraryCard = Just $ defaultEvent "ToggleTemplateLibraryCard"
  toEvent ToggleSetupConfirmationCard = Just $ defaultEvent "ToggleSetupConfirmationCard"
  toEvent (SetContractNickname _) = Just $ defaultEvent "SetContractNickname"
  toEvent (SetRoleWallet _ _) = Just $ defaultEvent "SetRoleWallet"
  toEvent (SetParameter _ _ _) = Just $ defaultEvent "SetParameter"
  toEvent StartContract = Just $ defaultEvent "StartContract"
