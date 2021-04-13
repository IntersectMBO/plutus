{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
-- | The log messages produced by the emulator.
module Wallet.Emulator.LogMessages(
  RequestHandlerLogMsg(..)
  , TxBalanceMsg(..)
  ) where

import           Data.Aeson                  (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc   (Pretty (..), hang, viaShow, vsep, (<+>))
import           GHC.Generics                (Generic)
import           Ledger                      (Address)
import           Ledger.Constraints.OffChain (UnbalancedTx)
import           Ledger.Slot                 (Slot)
import           Ledger.Value                (Value)
import           Wallet.Emulator.Error       (WalletAPIError)

data RequestHandlerLogMsg =
    SlotNoficationTargetVsCurrent Slot Slot
    | StartWatchingContractAddresses
    | HandleNextTxAt Slot Slot
    | HandleTxFailed WalletAPIError
    | UtxoAtFailed Address
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty RequestHandlerLogMsg where
    pretty = \case
        SlotNoficationTargetVsCurrent target current ->
            "target slot:" <+> pretty target <> "; current slot:" <+> pretty current
        StartWatchingContractAddresses -> "Start watching contract addresses"
        HandleTxFailed e -> "handleTx failed:" <+> viaShow e
        HandleNextTxAt current target ->
            "handle next tx at. Target:"
                <+> pretty target
                <+> "Current:"
                <+> pretty current
        UtxoAtFailed addr -> "UtxoAt failed:" <+> pretty addr

data TxBalanceMsg =
    BalancingUnbalancedTx UnbalancedTx
    | NoOutputsAdded
    | AddingPublicKeyOutputFor Value
    | NoInputsAdded
    | AddingInputsFor Value
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty TxBalanceMsg where
    pretty = \case
        BalancingUnbalancedTx utx   -> hang 2 $ vsep ["Balancing an unbalanced transaction:", pretty utx]
        NoOutputsAdded              -> "No outputs added"
        AddingPublicKeyOutputFor vl -> "Adding public key output for" <+> pretty vl
        NoInputsAdded               -> "No inputs added"
        AddingInputsFor vl          -> "Adding inputs for" <+> pretty vl
