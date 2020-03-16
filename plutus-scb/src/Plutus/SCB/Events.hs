{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell    #-}

module Plutus.SCB.Events
    ( module Events.Contract
    , module Events.User
    , module Events.Node
    , module Events.Wallet
    , ChainEvent(..)
    , _RecordRequest
    , _RecordResponse
    , _UserEvent
    , _NodeEvent
    , _WalletEvent
    ) where

import           Control.Lens.TH
import           Data.Aeson                 (FromJSON, ToJSON)
import           GHC.Generics               (Generic)
import           Plutus.SCB.Events.Contract as Events.Contract
import           Plutus.SCB.Events.Node     as Events.Node
import           Plutus.SCB.Events.User     as Events.User
import           Plutus.SCB.Events.Wallet   as Events.Wallet

-- | A structure which ties together all possible event types into one parent.
data ChainEvent
    = RecordRequest
          !(Events.Contract.RequestEvent Events.Contract.ContractRequest)
    | RecordResponse
          !(Events.Contract.ResponseEvent Events.Contract.ContractResponse)
    | UserEvent !Events.User.UserEvent
    | NodeEvent !Events.Node.NodeEvent
    | WalletEvent !Events.Wallet.WalletEvent
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

makePrisms ''ChainEvent
