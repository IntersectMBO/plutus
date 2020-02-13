{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Plutus.SCB.Events.Node
    ( NodeEvent(..)
    ) where

import           Data.Aeson   (FromJSON, ToJSON)
import           GHC.Generics (Generic)

import           Ledger       (Slot, Tx)

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
