{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
module Plutus.SCB.Events.Contract(
  -- $contract-events
  EventId(..)
  , Event(..)
  , RequestEvent(..)
  , ResponseEvent(..)
  , ContractRequest(..)
  , ContractRequestEvent
  , ContractResponse(..)
  , ContractResponseEvent
  ) where

import           Data.Aeson                               (Value)
import           Data.Text                                (Text)
import           GHC.Generics                             (Generic)

import qualified Language.Plutus.Contract.Effects.WriteTx as W
import           Language.Plutus.Contract.Tx              (UnbalancedTx)
import           Ledger.Address                           (Address)
import           Ledger.Crypto                            (PubKey)
import           Ledger.Slot                              (Slot)
import           Ledger.Tx                                (Tx)
import           Ledger.TxId                              (TxId)

import           Language.Plutus.Contract.Effects.UtxoAt  (UtxoAtAddress)

-- $contract-events
-- The events that compiled Plutus contracts are concerned with. For each type
-- of event there is a request constructor in 'ContractRequest' and a response
-- constructor in 'ContractResponse'.

{- note [Contract Events ]

Each contract instance has two event queues in the SCB: One for the requests
it makes, typed 'ContractRequestEvent', and one for the responses it receives,
typed 'ContractResponseEvent'.

The contract instances themselves deal with *sets of active endpoints* instead of
requests and responses directly. When the set of active endpoints of an instance
changes, the SCB needs to translate the change into 'ContractRequestEvent' values
by creating 'IssueRequest' events for the endpoints that have been added (compared
to the previous set of active endpoints) and creating 'CancelRequest' values for
endpoints that have disappeared.

-}

-- | Generic event ID
newtype EventId = EventId { unEventId :: Int } -- stand-in for whatever we end up using
  deriving stock (Eq, Ord, Show, Generic)

-- | Event with a unique identifier.
data Event p = Event { eventId :: EventId, eventPayload :: p }
  deriving stock (Eq, Ord, Show, Generic)

data RequestEvent e =
  IssueRequest e
  | CancelRequest EventId

data ResponseEvent e = ResponseEvent { respRequestId :: EventId, respPayload :: e }

data ContractRequest =
  AwaitSlotRequest Slot -- ^ Wait until a slot number is reached
  | AwaitTxConfirmedRequest TxId -- ^ Wait for a transaction to be confirmed (deeper than k blocks) TODO: confirmation levels
  | UserEndpointRequest Text -- ^ Expose a named endpoint to the user. The endpoint's schema can be obtained statically from the contract, so it is not included in the message. The response contains a JSON value that should adhere to the endpoint's schema.
  | OwnPubkeyRequest -- ^ Request a public key. It is expected that the wallet treats any outputs locked by this public key as part of its own funds.
  | UtxoAtRequest Address -- ^ Get the unspent transaction outputs at the address.
  | NextTxAtRequest Address -- ^ Wait for the next transaction that modifies the UTXO at the address and return it. TODO: confirmation levels
  | WriteTxRequest UnbalancedTx -- ^ Submit an unbalanced transaction to the SCB.
  deriving stock (Eq, Show, Generic)

type ContractRequestEvent = RequestEvent ContractRequest

data ContractResponse =
  AwaitSlotResponse Slot
  | AwaitTxConfirmedResponse TxId
  | UserEndpointResponse Value
  | OwnPubkeyResponse PubKey
  | UtxoAtResponse UtxoAtAddress
  | NextTxAtResponse Tx
  | WriteTxResponse W.WriteTxResponse
  deriving stock (Eq, Show, Generic)

type ContractResponseEvent = ResponseEvent ContractResponse
