module Template.Types
  ( State
  , SetupProgress(..)
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
    , editingNickname :: Boolean
    , setupProgress :: SetupProgress
    }

data SetupProgress
  = Roles
  | Parameters
  | Review

derive instance eqSetupProgress :: Eq SetupProgress

data Action
  = SetTemplate ContractTemplate
  | ToggleTemplateLibraryCard
  | ToggleSetupConfirmationCard
  | ToggleEditingNickname
  | SetContractNickname String
  | SetSetupProgress SetupProgress
  | SetRoleWallet String String
  | SetParameter IntegerTemplateType String (Maybe BigInteger)
  | StartContract

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (SetTemplate _) = Just $ defaultEvent "SetTemplate"
  toEvent ToggleTemplateLibraryCard = Nothing
  toEvent ToggleSetupConfirmationCard = Nothing
  toEvent ToggleEditingNickname = Nothing
  toEvent (SetContractNickname _) = Just $ defaultEvent "SetContractNickname"
  toEvent (SetSetupProgress _) = Nothing
  toEvent (SetRoleWallet _ _) = Just $ defaultEvent "SetRoleWallet"
  toEvent (SetParameter _ _ _) = Just $ defaultEvent "SetParameter"
  toEvent StartContract = Just $ defaultEvent "StartContract"
