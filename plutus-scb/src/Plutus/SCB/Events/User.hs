{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Plutus.SCB.Events.User where

import           Data.Aeson       (FromJSON, ToJSON)
import           GHC.Generics     (Generic)
import           Plutus.SCB.Types (ActiveContractState)

-- | Users can install contracts and transition them to a new state.
--   Contracts are identified by values of 't'.
data UserEvent t
    = InstallContract !t
    | ContractStateTransition !(ActiveContractState t)
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)
