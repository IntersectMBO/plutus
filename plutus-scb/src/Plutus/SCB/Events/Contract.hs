{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
module Plutus.SCB.Events.Contract(
  -- $contract-events
  ContractEvent(..)
  , ContractInstanceId(..)
  , ContractIteration(..)
  , iterationZero
  , ContractRequest(..)
  , ContractResponse(..)
  , PartiallyDecodedResponse(..)
  , ContractInstanceState(..)
  , ContractMailbox(..)
  , MailboxMessage(..)
  -- * Prisms
  -- ** ContractRequest
  , _AwaitSlotRequest
  , _AwaitTxConfirmedRequest
  , _UserEndpointRequest
  , _OwnPubkeyRequest
  , _UtxoAtRequest
  , _NextTxAtRequest
  , _WriteTxRequest
  -- ** ContractResponse
  , _AwaitSlotResponse
  , _AwaitTxConfirmedResponse
  , _UserEndpointResponse
  , _OwnPubkeyResponse
  , _UtxoAtResponse
  , _NextTxAtResponse
  , _WriteTxResponse
  -- ** ContractEvent
  , _ContractMailboxEvent
  , _ContractInstanceStateUpdateEvent
  -- ** Mailbox
  , _InboxMessage
  , _OutboxMessage
  ) where

import           Control.Lens.TH                                   (makePrisms)
import           Data.Aeson                                        (FromJSON, FromJSONKey, ToJSON, ToJSONKey, Value)
import qualified Data.Aeson.Encode.Pretty                          as JSON
import qualified Data.ByteString.Lazy.Char8                        as BS8
import           Data.Semigroup                                    (Max (..))
import           Data.Text                                         (Text)
import qualified Data.Text                                         as Text
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Extras                  (PrettyShow (..))
import           Data.UUID                                         (UUID)
import           GHC.Generics                                      (Generic)

import qualified Language.Plutus.Contract.Effects.WriteTx          as W
import           Ledger.Address                                    (Address)
import           Ledger.Crypto                                     (PubKey)
import           Ledger.Slot                                       (Slot)
import           Ledger.Tx                                         (Tx)

import           Language.Plutus.Contract.Effects.AwaitSlot        (WaitingForSlot)
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..), TxIdSet)
import           Language.Plutus.Contract.Effects.ExposeEndpoint   (ActiveEndpoints, EndpointValue)
import           Language.Plutus.Contract.Effects.OwnPubKey        (OwnPubKeyRequest)
import           Language.Plutus.Contract.Effects.UtxoAt           (UtxoAtAddress)
import           Language.Plutus.Contract.Effects.WatchAddress     (AddressSet)
import           Language.Plutus.Contract.Effects.WriteTx          (PendingTransactions)
import           Numeric.Natural                                   (Natural)

import           Plutus.SCB.Utils                                  (abbreviate)

-- $contract-events
-- The events that compiled Plutus contracts are concerned with. For each type
-- of event there is a request constructor in 'ContractRequest' and a response
-- constructor in 'ContractResponse'.

{- Note [Contract Events]

Each contract instance has two event queues in the SCB: One for the requests
it makes, typed 'ContractOutboxMessage', and one for the responses it receives,
typed 'ContractInboxMessage'.

-}

{- Note [Contract Iterations]

Contracts are executed iteratively:

* We look at the current state of the contract to see which requests (hooks)
  it wants to make
* We process one of those requests and feed the result to the contract
* The contract produces a new state, which we again inspect to get the hooks
  that are currently active

In each iteration we only feed one event to the contract, so if there is more
than one hook then the other ones will be un-answered.  If the contract had
been waiting for the first of several possible events, then the other hooks
will disappear from the set of active hooks. But if it had been waiting for
all of those events to happen then the remaining hooks will appear in the
result, and we handle them in the next iteration.

So each iteration begins with a set of requests from the contract and ends with
one of those requests being handled.

-}

-- | Unique ID for contract instance
newtype ContractInstanceId = ContractInstanceId { unContractInstanceId :: UUID }
    deriving  (Eq, Ord, Show, Generic)
    deriving newtype (FromJSON, ToJSON, FromJSONKey, ToJSONKey)
    deriving Pretty via (PrettyShow UUID)

-- | How many times the contract has been advanced (how many events have been
--   fed to it)
newtype ContractIteration = ContractIteration { unContractIteration :: Natural }
    deriving  (Eq, Ord, Show, Generic)
    deriving newtype (FromJSON, ToJSON, Pretty, Enum)
    deriving Semigroup via (Max Natural)

instance Monoid ContractIteration where
    mappend = (<>)
    mempty  = ContractIteration 0

iterationZero :: ContractIteration
iterationZero = mempty

data ContractRequest =
  AwaitSlotRequest WaitingForSlot -- ^ Wait until a slot number is reached
  | AwaitTxConfirmedRequest TxIdSet -- ^ Wait for a transaction to be confirmed (deeper than k blocks) TODO: confirmation levels
  | UserEndpointRequest ActiveEndpoints -- ^ Expose a set of named endpoint to the user. The endpoints' schemas can be obtained statically from the contract (using 'Language.Plutus.Contract.IOTS.rowSchema'), so they are not included in the message.
  | OwnPubkeyRequest OwnPubKeyRequest -- ^ Request a public key. It is expected that the wallet treats any outputs locked by this public key as part of its own funds.
  | UtxoAtRequest AddressSet -- ^ Get the unspent transaction outputs at the address.
  | NextTxAtRequest AddressSet -- ^ Wait for the next transaction that modifies the UTXO at the address and return it. TODO: confirmation levels
  | WriteTxRequest PendingTransactions -- ^ Submit an unbalanced transaction to the SCB.
  deriving  (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

instance Pretty ContractRequest where
    pretty = \case
        AwaitSlotRequest s -> "AwaitSlot:" <+> pretty s
        AwaitTxConfirmedRequest t -> "AwaitTxConfirmed:" <+> pretty t
        UserEndpointRequest t -> "UserEndpoint:" <+> pretty t
        OwnPubkeyRequest r -> "OwnPubKey:" <+> pretty r
        UtxoAtRequest a -> "UtxoAt:" <+> pretty a
        NextTxAtRequest a -> "NextTxAt:" <+> pretty a
        WriteTxRequest u -> "WriteTx:" <+> pretty u

data ContractResponse =
  AwaitSlotResponse Slot
  | AwaitTxConfirmedResponse TxConfirmed
  | UserEndpointResponse Text (EndpointValue Value)
  | OwnPubkeyResponse PubKey
  | UtxoAtResponse UtxoAtAddress
  | NextTxAtResponse (Address, Tx)
  | WriteTxResponse W.WriteTxResponse
  deriving  (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

instance Pretty ContractResponse where
    pretty = \case
        AwaitSlotResponse s        -> "AwaitSlot:" <+> pretty s
        UserEndpointResponse n r     -> "UserEndpoint:" <+> pretty n <+> pretty r
        OwnPubkeyResponse pk       -> "OwnPubKey:" <+> pretty pk
        UtxoAtResponse utxo        -> "UtxoAt:" <+> pretty utxo
        NextTxAtResponse r         -> "NextTxAt:" <+> pretty r
        WriteTxResponse w          -> "WriteTx:" <+> pretty w
        AwaitTxConfirmedResponse w -> "AwaitTxConfirmed:" <+> pretty w

data ContractInstanceState t =
    ContractInstanceState
        { csContract           :: ContractInstanceId
        , csCurrentIteration   :: ContractIteration
        , csCurrentState       :: PartiallyDecodedResponse
        , csContractDefinition :: t
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty t => Pretty (ContractInstanceState t) where
    pretty ContractInstanceState{csContract, csCurrentIteration, csCurrentState, csContractDefinition} =
        hang 2 $ vsep
            [ "Instance:" <+> pretty csContract
            , "Iteration:" <+> pretty csCurrentIteration
            , "State:" <+> pretty csCurrentState
            , "Contract definition:" <+> pretty csContractDefinition
            ]

data PartiallyDecodedResponse =
    PartiallyDecodedResponse
        { newState :: Value
        , hooks    :: Value
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty PartiallyDecodedResponse where
    pretty PartiallyDecodedResponse {newState, hooks} =
        vsep
            [ "State:"
            , indent 2 $ pretty $ abbreviate 120 $ Text.pack $ BS8.unpack $ JSON.encodePretty newState
            , "Hooks:"
            , indent 2 $ pretty $ BS8.unpack $ JSON.encodePretty hooks
            ]

data ContractMailbox =
    ContractMailbox
        { cmInstance  :: ContractInstanceId
        , cmIteration :: ContractIteration
        }  deriving (Show, Eq, Generic)
        deriving anyclass (FromJSON, ToJSON)

instance Pretty ContractMailbox where
    pretty ContractMailbox{cmInstance, cmIteration} =
        hang 2 $ vsep
        [ "Instance:" <+> pretty cmInstance
        , "Iteration:" <+> pretty cmIteration
        ]

data MailboxMessage =
    OutboxMessage ContractRequest | InboxMessage ContractResponse
    deriving stock (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty MailboxMessage where
    pretty = \case
        InboxMessage msg -> "InboxMessage:" <+> pretty msg
        OutboxMessage msg -> "OutboxMessage:" <+> pretty msg

data ContractEvent t =
    ContractMailboxEvent ContractMailbox MailboxMessage
    | ContractInstanceStateUpdateEvent (ContractInstanceState t)
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty t => Pretty (ContractEvent t) where
    pretty = \case
        ContractMailboxEvent mbx msg -> "Mailbox:" <+> pretty mbx <+> pretty msg
        ContractInstanceStateUpdateEvent m -> "StateUpdate:" <+> pretty m

makePrisms ''MailboxMessage
makePrisms ''ContractRequest
makePrisms ''ContractResponse
makePrisms ''ContractEvent
