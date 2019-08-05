{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
module Language.Plutus.Contract.Prompt.Event(
      Event(..)
    -- * Produce events
    , updateLedger
    , changeSlot
    , endpoint
    , endpointJson
    , txSubmission
    , txEvents
    -- * Consume events
    , ledgerUpdate
    , slotChange
    , endpointEvent
    , txSubmissionEvent
    ) where

import qualified Data.Aeson        as Aeson
import           Data.Map          (Map)
import qualified Data.Map          as Map
import           GHC.Generics      (Generic)

import           Ledger.AddressMap (AddressMap)
import qualified Ledger.AddressMap as AM
import           Ledger.Slot       (Slot)
import           Ledger.Tx         (Address, Tx)

-- | An event that happened on the blockchain or as a result of a user action.
--   See note [Hooks and Events] in 'Language.Plutus.Contract.Effects'.
data Event =
    LedgerUpdate Address Tx
    | TxSubmission -- TODO: add more events about specific transactions (namely, tx submitted, tx rejected, tx rolled back, etc.)
    | SlotChange Slot
    | Endpoint String Aeson.Value
    deriving stock (Eq, Show, Generic)
    deriving anyclass (Aeson.FromJSON, Aeson.ToJSON) -- TODO: Make sure this can be created easily by app platform

txEvents :: AddressMap -> Tx -> Map Address Event
txEvents utxo t = Map.fromSet (`updateLedger` t) (AM.addressesTouched utxo t)

updateLedger :: Address -> Tx -> Event
updateLedger = LedgerUpdate

changeSlot :: Slot -> Event
changeSlot = SlotChange

endpoint :: String -> Aeson.Value -> Event
endpoint = Endpoint

endpointJson :: Aeson.ToJSON a => String -> a -> Event
endpointJson n = Endpoint n . Aeson.toJSON

txSubmission :: Event
txSubmission = TxSubmission

ledgerUpdate :: Event -> Maybe (Address, Tx)
ledgerUpdate = \case
    LedgerUpdate a t -> Just (a, t)
    _ -> Nothing

slotChange :: Event -> Maybe Slot
slotChange = \case
    SlotChange sl -> Just sl
    _ -> Nothing

endpointEvent :: Event -> Maybe (String, Aeson.Value)
endpointEvent = \case
    Endpoint s v -> Just (s, v)
    _ -> Nothing

txSubmissionEvent :: Event -> Maybe ()
txSubmissionEvent = \case
    TxSubmission -> Just ()
    _ -> Nothing
