{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}

module Plutus.SCB.Events.Node
    ( NodeEvent(..)
    ) where

import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)

import           Ledger                    (Slot, Tx, txId)

data NodeEvent
    = BlockAdded [Tx]
  -- ^ A new block was added to the blockchain
    | NewSlot Slot
  -- ^ A new slot has been added
    | SubmittedTx Tx
  -- ^ Confirmation that the transactions were received.
  -- TODO: Rollbacks?
  -- | Rollback Int -- ^ n blocks were rolled back
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty NodeEvent where
  pretty = \case
    BlockAdded blck -> "BlockAdded:" <+> pretty (txId <$> blck)
    NewSlot slt -> "NewSlot:" <+> pretty slt
    SubmittedTx tx -> "SubmittedTx:" <+> pretty tx
