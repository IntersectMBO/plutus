{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
module Language.PlutusTx.Coordination.Contracts.Auction(
    AuctionState(..),
    AuctionInput(..)
    ) where

import           Data.Aeson   (FromJSON, ToJSON)
import           GHC.Generics (Generic)
import           Ledger       (PubKeyHash, Slot, Value)

-- BLOCK1

-- | Definition of an auction
data AuctionParams
    = AuctionParams
        { apOwner   :: PubKeyHash -- ^ Current owner of the asset. This is where the proceeds of the auction will be sent.
        , apAsset   :: Value -- ^ The asset itself. This value is going to be locked by the auction script output.
        , apEndTime :: Slot -- ^ When the time window for bidding ends.
        }

-- BLOCK2
-- | The states of the auction
data AuctionState
    = Ongoing { highestBid :: Ada, highestBidder :: PubKeyHash } -- Bids can be submitted
    | Finished -- The auction is finished
    deriving stock (Generic, Show)
    deriving anyclass (ToJSON, FromJSON)

-- | Transition between auction states
data AuctionInput
    = Bid { newBid :: Ada, newBidder :: PubKeyHash } -- Increase the price
    | Payout
    deriving stock (Generic, Show)
    deriving anyclass (ToJSON, FromJSON)
-- BLOCK3
