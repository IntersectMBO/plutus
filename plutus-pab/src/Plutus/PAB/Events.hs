{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutus.PAB.Events
    ( module Events.Contract
    , module Events.User
    , module Events.Node
    , module Events.Wallet
    , ChainEvent(..)
    , _UserEvent
    , _NodeEvent
    , _WalletEvent
    -- , _ContractEvent
    ) where

import           Control.Lens.TH             (makePrisms)
import           Data.Aeson                  (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc   (Pretty, pretty, (<+>))
import           GHC.Generics                (Generic)
import           Plutus.PAB.Effects.Contract (PABContract (..))
import           Plutus.PAB.Events.Contract  as Events.Contract
import           Plutus.PAB.Events.Node      as Events.Node
import           Plutus.PAB.Events.User      as Events.User
import           Plutus.PAB.Events.Wallet    as Events.Wallet

-- | A structure which ties together all possible event types into one parent.
data ChainEvent t =
    UserEvent !(Events.User.UserEvent t)
    | NodeEvent !Events.Node.NodeEvent
    | WalletEvent !Events.Wallet.WalletEvent
    deriving stock Generic

deriving stock instance Show (ContractDef t) => Show (ChainEvent t)
deriving stock instance Eq (ContractDef t) => Eq (ChainEvent t)

deriving anyclass instance FromJSON (ContractDef t) => FromJSON (ChainEvent t)
deriving anyclass instance ToJSON (ContractDef t) => ToJSON (ChainEvent t)

makePrisms ''ChainEvent

instance Pretty (ContractDef t) => Pretty (ChainEvent t) where
    pretty = \case
        UserEvent t   -> "UserEvent:" <+> pretty t
        NodeEvent t   -> "NodeEvent:" <+> pretty t
        WalletEvent t -> "WalletEvent:" <+> pretty t
        -- ContractEvent t -> "ContractEvent:" <+> pretty t
