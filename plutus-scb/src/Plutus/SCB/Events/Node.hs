{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
module Plutus.SCB.Events.Node(
  NodeEvent(..)
  ) where

import           Data.Aeson  (FromJSON, ToJSON)
import GHC.Generics (Generic)

import           Ledger.Slot (Slot)
import           Ledger.Tx   (Tx)

data NodeEvent =
  BlockAdded [Tx]
  -- ^ A new block was added to the blockchain
  | NewSlot Slot
  -- ^ A new slot has been added
  -- TODO: Rollbacks?
  -- | Rollback Int -- ^ n blocks were rolled back
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)
