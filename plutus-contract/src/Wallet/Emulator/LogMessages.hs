{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
-- | The log messages produced by the emulator.
module Wallet.Emulator.LogMessages(
  RequestHandlerLogMsg(..)
  , TxBalanceMsg(..)
  , _ValidationFailed
  ) where

import           Control.Lens.TH             (makePrisms)
import           Data.Aeson                  (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc   (Pretty (..), colon, hang, viaShow, vsep, (<+>))
import           GHC.Generics                (Generic)
import           Ledger                      (Address, Tx, TxId, txId)
import           Ledger.Constraints.OffChain (UnbalancedTx)
import           Ledger.Index                (ScriptValidationEvent, ValidationError, ValidationPhase)
import           Ledger.Slot                 (Slot, SlotRange)
import           Ledger.Value                (Value)
import           Wallet.Emulator.Error       (WalletAPIError)

data RequestHandlerLogMsg =
    SlotNoticationTargetVsCurrent Slot Slot
    | StartWatchingContractAddresses
    | HandleAddressChangedAt Slot SlotRange
    | HandleTxFailed WalletAPIError
    | UtxoAtFailed Address
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty RequestHandlerLogMsg where
    pretty = \case
        SlotNoticationTargetVsCurrent target current ->
            "target slot:" <+> pretty target <> "; current slot:" <+> pretty current
        StartWatchingContractAddresses -> "Start watching contract addresses"
        HandleTxFailed e -> "handleTx failed:" <+> viaShow e
        HandleAddressChangedAt current slotRange ->
            "handle address changed at. Range:"
                <+> pretty slotRange
                <+> "Current:"
                <+> pretty current
        UtxoAtFailed addr -> "UtxoAt failed:" <+> pretty addr

data TxBalanceMsg =
    BalancingUnbalancedTx UnbalancedTx
    | NoOutputsAdded
    | AddingPublicKeyOutputFor Value
    | NoInputsAdded
    | AddingInputsFor Value
    | NoCollateralInputsAdded
    | AddingCollateralInputsFor Value
    | FinishedBalancing Tx
    | SubmittingTx Tx
    | ValidationFailed ValidationPhase TxId Tx ValidationError [ScriptValidationEvent]
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty TxBalanceMsg where
    pretty = \case
        BalancingUnbalancedTx utx    -> hang 2 $ vsep ["Balancing an unbalanced transaction:", pretty utx]
        NoOutputsAdded               -> "No outputs added"
        AddingPublicKeyOutputFor vl  -> "Adding public key output for" <+> pretty vl
        NoInputsAdded                -> "No inputs added"
        AddingInputsFor vl           -> "Adding inputs for" <+> pretty vl
        NoCollateralInputsAdded      -> "No collateral inputs added"
        AddingCollateralInputsFor vl -> "Adding collateral inputs for" <+> pretty vl
        FinishedBalancing tx         -> "Finished balancing." <+> pretty (txId tx)
        SubmittingTx tx              -> "Submitting tx:" <+> pretty (txId tx)
        ValidationFailed p i _ e _   -> "Validation error:" <+> pretty p <+> pretty i <> colon <+> pretty e

makePrisms ''TxBalanceMsg
