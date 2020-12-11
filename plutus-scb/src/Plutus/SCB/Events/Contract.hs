{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Plutus.SCB.Events.Contract(
  -- $contract-events
  ContractEvent(..)
  , ContractInstanceId(..)
  , IterationID
  , ContractSCBRequest(..)
  , ContractHandlersResponse(..)
  , ContractResponse(..)
  , PartiallyDecodedResponse(..)
  , hasActiveRequests
  , ContractInstanceState(..)
  -- * Prisms
  -- ** ContractRequest
  , _AwaitSlotRequest
  , _AwaitTxConfirmedRequest
  , _UserEndpointRequest
  , _OwnPubkeyRequest
  , _UtxoAtRequest
  , _NextTxAtRequest
  , _WriteTxRequest
  , _OwnInstanceIdRequest
  , _SendNotificationRequest
  -- ** ContractResponse
  , _AwaitSlotResponse
  , _AwaitTxConfirmedResponse
  , _UserEndpointResponse
  , _OwnPubkeyResponse
  , _UtxoAtResponse
  , _NextTxAtResponse
  , _WriteTxResponse
  , _OwnInstanceResponse
  , _NotificationResponse
  -- ** ContractEvent
  , _ContractInboxMessage
  , _ContractInstanceStateUpdateEvent
  ) where

import           Control.Lens.TH                                   (makePrisms)
import           Control.Monad.Freer.Log                           (LogMessage)
import           Data.Aeson                                        (FromJSON, ToJSON, Value, (.:))
import qualified Data.Aeson                                        as JSON
import qualified Data.Aeson.Encode.Pretty                          as JSON
import qualified Data.ByteString.Lazy.Char8                        as BS8
import qualified Data.Text                                         as Text
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                                      (Generic)

import qualified Language.Plutus.Contract.Effects.WriteTx          as W
import           Language.Plutus.Contract.Resumable                (IterationID)
import qualified Language.Plutus.Contract.Resumable                as Contract
import qualified Language.Plutus.Contract.State                    as Contract
import           Ledger                                            (TxId)
import           Ledger.Address                                    (Address)
import           Ledger.Constraints.OffChain                       (UnbalancedTx)
import           Ledger.Crypto                                     (PubKey)
import           Ledger.Slot                                       (Slot)

import           Language.Plutus.Contract.Effects.AwaitSlot        (WaitingForSlot)
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..))
import           Language.Plutus.Contract.Effects.ExposeEndpoint   (ActiveEndpoint (..), EndpointDescription (..),
                                                                    EndpointValue)
import           Language.Plutus.Contract.Effects.Instance         (OwnIdRequest)
import           Language.Plutus.Contract.Effects.OwnPubKey        (OwnPubKeyRequest)
import           Language.Plutus.Contract.Effects.UtxoAt           (UtxoAtAddress)

import           Plutus.SCB.Utils                                  (abbreviate)
import           Wallet.Effects                                    (AddressChangeRequest, AddressChangeResponse)
import           Wallet.Types                                      (ContractInstanceId (..), Notification,
                                                                    NotificationError)

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

data ContractSCBRequest =
  AwaitSlotRequest WaitingForSlot -- ^ Wait until a slot number is reached
  | AwaitTxConfirmedRequest TxId -- ^ Wait for a transaction to be confirmed (deeper than k blocks) TODO: confirmation levels
  | UserEndpointRequest ActiveEndpoint -- ^ Expose a named endpoint to the user. The endpoints' schemas can be obtained statically from the contract (using 'Language.Plutus.Contract.IOTS.rowSchema'), so they are not included in the message.
  | OwnPubkeyRequest OwnPubKeyRequest -- ^ Request a public key. It is expected that the wallet treats any outputs locked by this public key as part of its own funds.
  | UtxoAtRequest Address -- ^ Get the unspent transaction outputs at the address.
  | NextTxAtRequest AddressChangeRequest -- ^ Wait for the next transaction that modifies the UTXO at the address and return it.
  | WriteTxRequest UnbalancedTx -- ^ Submit an unbalanced transaction to the SCB.
  | OwnInstanceIdRequest OwnIdRequest -- ^ Request the ID of the contract instance.
  | SendNotificationRequest Notification -- ^ Send a notification to another contract instance
  deriving  (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | 'ContractSCBRequest' with a 'FromJSON' instance that is compatible with
--   the 'ToJSON' instance of 'Language.Plutus.Contract.Schema.Handlers'.
newtype ContractHandlersResponse = ContractHandlersResponse { unContractHandlersResponse :: ContractSCBRequest }

instance FromJSON ContractHandlersResponse where
    parseJSON = JSON.withObject "ContractHandlersResponse" $ \v -> ContractHandlersResponse <$> do
        (tag :: Text.Text) <- v .: "tag"
        case tag of
            "slot"            -> AwaitSlotRequest <$> v .: "value"
            "tx-confirmation" -> AwaitTxConfirmedRequest <$> v .: "value"
            "own-pubkey"      -> OwnPubkeyRequest <$> v .: "value"
            "utxo-at"         -> UtxoAtRequest <$> v.: "value"
            "address"         -> NextTxAtRequest <$> v .: "value"
            "tx"              -> WriteTxRequest <$> v .: "value"
            "own-instance-id" -> OwnInstanceIdRequest <$> v .: "value"
            "notify"          -> SendNotificationRequest <$> v .: "value"
            _                 -> UserEndpointRequest <$> v .: "value"

instance Pretty ContractSCBRequest where
    pretty = \case
        AwaitSlotRequest s        -> "AwaitSlot:" <+> pretty s
        AwaitTxConfirmedRequest t -> "AwaitTxConfirmed:" <+> pretty t
        UserEndpointRequest t     -> "UserEndpoint:" <+> pretty t
        OwnPubkeyRequest r        -> "OwnPubKey:" <+> pretty r
        UtxoAtRequest a           -> "UtxoAt:" <+> pretty a
        NextTxAtRequest a         -> "NextTxAt:" <+> pretty a
        WriteTxRequest u          -> "WriteTx:" <+> pretty u
        OwnInstanceIdRequest r    -> "OwnInstanceId:" <+> pretty r
        SendNotificationRequest n -> "Notification:" <+> pretty n

data ContractResponse =
  AwaitSlotResponse Slot
  | AwaitTxConfirmedResponse TxConfirmed
  | UserEndpointResponse EndpointDescription (EndpointValue Value)
  | OwnPubkeyResponse PubKey
  | UtxoAtResponse UtxoAtAddress
  | NextTxAtResponse AddressChangeResponse
  | WriteTxResponse W.WriteTxResponse
  | OwnInstanceResponse ContractInstanceId
  | NotificationResponse (Maybe NotificationError)
  deriving  (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

instance Pretty ContractResponse where
    pretty = \case
        AwaitSlotResponse s        -> "AwaitSlot:" <+> pretty s
        UserEndpointResponse n r   -> "UserEndpoint:" <+> pretty n <+> pretty r
        OwnPubkeyResponse pk       -> "OwnPubKey:" <+> pretty pk
        UtxoAtResponse utxo        -> "UtxoAt:" <+> pretty utxo
        NextTxAtResponse rsp       -> "NextTxAt:" <+> pretty rsp
        WriteTxResponse w          -> "WriteTx:" <+> pretty w
        AwaitTxConfirmedResponse w -> "AwaitTxConfirmed:" <+> pretty w
        OwnInstanceResponse r      -> "OwnInstance:" <+> pretty r
        NotificationResponse r     -> "Notification:" <+> pretty r

data ContractInstanceState t =
    ContractInstanceState
        { csContract           :: ContractInstanceId
        , csCurrentIteration   :: IterationID
        , csCurrentState       :: PartiallyDecodedResponse ContractSCBRequest
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

data PartiallyDecodedResponse v =
    PartiallyDecodedResponse
        { newState :: Contract.State Value
        , hooks    :: [Contract.Request v]
        , logs     :: [LogMessage Value]
        }
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty v => Pretty (PartiallyDecodedResponse v) where
    pretty PartiallyDecodedResponse {newState, hooks} =
        vsep
            [ "State:"
            , indent 2 $ pretty $ abbreviate 120 $ Text.pack $ BS8.unpack $ JSON.encodePretty newState
            , "Hooks:"
            , indent 2 (vsep $ pretty <$> hooks)
            ]

data ContractEvent t =
    ContractInboxMessage ContractInstanceId (Contract.Response ContractResponse)
    | ContractInstanceStateUpdateEvent (ContractInstanceState t)
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty t => Pretty (ContractEvent t) where
    pretty = \case
        ContractInboxMessage mbx sb        -> "InboxMessage:" <+> pretty mbx <+> pretty sb
        ContractInstanceStateUpdateEvent m -> "StateUpdate:" <+> pretty m

makePrisms ''ContractSCBRequest
makePrisms ''ContractResponse
makePrisms ''ContractEvent

hasActiveRequests :: ContractInstanceState t -> Bool
hasActiveRequests = not . null . hooks . csCurrentState
