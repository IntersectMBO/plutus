{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}

module Plutus.SCB.Events.User where

import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics               (Generic)
import           Plutus.SCB.Events.Contract (ContractInstanceState)

-- | Users can install contracts and transition them to a new state.
--   Contracts are identified by values of 't'.
data UserEvent t
    = InstallContract !t
    | ContractStateTransition !(ContractInstanceState t)
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty t => Pretty (UserEvent t) where
    pretty = \case
        InstallContract t -> "InstallContract:" <+> pretty t
        ContractStateTransition s -> "ContractStateTransition:" <+> pretty s
