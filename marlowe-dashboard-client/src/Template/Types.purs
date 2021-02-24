module Template.Types
  ( State
  , Template
  , MetaData
  , ContractSetupScreen(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.BigInteger (BigInteger)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Marlowe.Extended (Contract, IntegerTemplateType, TemplateContent)
import Marlowe.Semantics (TokenName)

type State
  = { template :: Template
    , contractNickname :: String
    , roleWallets :: Map String String
    , templateContent :: TemplateContent
    }

type Template
  = { metaData :: MetaData
    , extendedContract :: Contract
    }

type MetaData
  = { contractName :: String
    , contractType :: String
    , contractDescription :: String
    , roleDescriptions :: Map TokenName String
    , slotParameterDescriptions :: Map String String
    , valueParameterDescriptions :: Map String String
    , choiceDescriptions :: Map String String
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
