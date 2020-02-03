{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Plutus.SCB.Events.User where

import           Data.Aeson       (FromJSON, ToJSON)
import           GHC.Generics     (Generic)
import           Plutus.SCB.Types (ActiveContractState, Contract)

data UserEvent
    = InstallContract Contract
    | ContractStateTransition ActiveContractState
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)
