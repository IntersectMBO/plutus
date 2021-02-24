module Template.Types
  ( State
  , Template
  , ContractSetupScreen(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.BigInteger (BigInteger)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Marlowe.Extended (Contract, IntegerTemplateType, TemplateContent)

type State
  = { template :: Template
    , contractNickname :: String
    , roleWallets :: Map String String
    , templateContent :: TemplateContent
    }

type Template
  = { name :: String
    , type_ :: String
    , description :: String
    , extendedContract :: Contract
    }

data ContractSetupScreen
  = ContractRolesScreen
  | ContractParametersScreen
  | ContractReviewScreen

derive instance eqContractSetupScreen :: Eq ContractSetupScreen

data Action
  = SetContractNickname String
  | SetRoleWallet String String
  | SetParameter IntegerTemplateType String (Maybe BigInteger)

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (SetContractNickname _) = Just $ defaultEvent "SetContractNickname"
  toEvent (SetRoleWallet _ _) = Just $ defaultEvent "SetRoleWallet"
  toEvent (SetParameter _ _ _) = Just $ defaultEvent "SetParameter"
