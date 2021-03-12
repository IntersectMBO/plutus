module Template.Types
  ( State
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.BigInteger (BigInteger)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Marlowe.Extended (IntegerTemplateType, TemplateContent)
import Marlowe.Extended.Template (ContractTemplate)

type State
  = { template :: ContractTemplate
    , contractNickname :: String
    -- FIXME: We should add type aliases to these Strings
    , roleWallets :: Map String String
    , templateContent :: TemplateContent
    }

data Action
  = SetTemplate ContractTemplate
  | ToggleTemplateLibraryCard
  | ToggleCreateWalletCard String
  | ToggleSetupConfirmationCard
  | SetContractNickname String
  | SetRoleWallet String String
  | SetParameter IntegerTemplateType String (Maybe BigInteger)
  | StartContract

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent (SetTemplate _) = Just $ defaultEvent "SetTemplate"
  toEvent ToggleTemplateLibraryCard = Nothing
  toEvent (ToggleCreateWalletCard tokenName) = Nothing
  toEvent ToggleSetupConfirmationCard = Nothing
  toEvent (SetContractNickname _) = Just $ defaultEvent "SetContractNickname"
  toEvent (SetRoleWallet _ _) = Just $ defaultEvent "SetRoleWallet"
  toEvent (SetParameter _ _ _) = Just $ defaultEvent "SetParameter"
  toEvent StartContract = Just $ defaultEvent "StartContract"
