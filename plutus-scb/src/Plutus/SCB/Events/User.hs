{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Plutus.SCB.Events.User where

import           Data.Aeson       (FromJSON, ToJSON)
import           GHC.Generics     (Generic)
import           Plutus.SCB.Types (ActiveContract,Contract, PartiallyDecodedResponse)

data UserEvent
    = InstallContract Contract
    | ContractStateTransition ActiveContract PartiallyDecodedResponse
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)
