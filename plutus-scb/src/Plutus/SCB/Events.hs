{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}

module Plutus.SCB.Events
    ( module Events.Contract
    , module Events.User
    , module Events.Node
    , module Events.Wallet
    , ChainEvent(..)
    , _UserEvent
    , _NodeEvent
    , _WalletEvent
    , _ContractEvent
    ) where

import           Control.Lens.TH
import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics               (Generic)
import           Plutus.SCB.Events.Contract as Events.Contract
import           Plutus.SCB.Events.Node     as Events.Node
import           Plutus.SCB.Events.User     as Events.User
import           Plutus.SCB.Events.Wallet   as Events.Wallet

-- | A structure which ties together all possible event types into one parent.
data ChainEvent t =
    UserEvent !(Events.User.UserEvent t)
    | NodeEvent !Events.Node.NodeEvent
    | WalletEvent !Events.Wallet.WalletEvent
    | ContractEvent !(Events.Contract.ContractEvent t)
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

makePrisms ''ChainEvent

instance Pretty t => Pretty (ChainEvent t) where
    pretty = \case
        UserEvent t -> "UserEvent:" <+> pretty t
        NodeEvent t -> "NodeEvent:" <+> pretty t
        WalletEvent t -> "WalletEvent:" <+> pretty t
        ContractEvent t -> "ContractEvent:" <+> pretty t
