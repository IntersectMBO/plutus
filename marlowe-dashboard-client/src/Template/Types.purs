module Template.Types
  ( State
  , Screen(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.BigInteger (BigInteger)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Marlowe.Extended (IntegerTemplateType, TemplateContent, ContractTemplate)

type State
  = { template :: ContractTemplate
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
  = SetTemplate ContractTemplate
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
