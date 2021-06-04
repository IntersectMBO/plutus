{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
module Plutus.PAB.Events.Contract(
  -- $contract-events
  ContractInstanceId(..)
  , IterationID
  , ContractPABRequest(..)
  , ContractHandlersResponse(..)
  , ContractHandlerRequest(..)
  , ContractPABResponse(..)
  -- * Prisms
  -- ** ContractRequest
  , _AwaitSlotRequest
  , _AwaitTxConfirmedRequest
  , _UserEndpointRequest
  , _OwnPubkeyRequest
  , _UtxoAtRequest
  , _AddressChangedAtRequest
  , _WriteTxRequest
  , _OwnInstanceIdRequest
  -- ** ContractResponse
  , _AwaitSlotResponse
  , _AwaitTxConfirmedResponse
  , _UserEndpointResponse
  , _OwnPubkeyResponse
  , _UtxoAtResponse
  , _AddressChangedAtResponse
  , _WriteTxResponse
  , _OwnInstanceResponse
  ) where

import           Control.Lens.TH                          (makePrisms)
import           Data.Aeson                               (FromJSON, ToJSON (..), Value, object, (.:), (.=))
import qualified Data.Aeson                               as JSON
import qualified Data.Text                                as Text
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                             (Generic)

import           Ledger                                   (TxId)
import           Ledger.Address                           (Address)
import           Ledger.Constraints.OffChain              (UnbalancedTx)
import           Ledger.Crypto                            (PubKey)
import           Ledger.Slot                              (Slot)
import qualified Plutus.Contract.Effects.AwaitSlot        as AwaitSlot
import qualified Plutus.Contract.Effects.AwaitTxConfirmed as AwaitTxConfirmed
import qualified Plutus.Contract.Effects.Instance         as Instance
import qualified Plutus.Contract.Effects.OwnPubKey        as OwnPubKey
import qualified Plutus.Contract.Effects.UtxoAt           as UtxoAt
import qualified Plutus.Contract.Effects.WatchAddress     as AddressChangedAt
import qualified Plutus.Contract.Effects.WriteTx          as W
import qualified Plutus.Contract.Effects.WriteTx          as WriteTx
import           Plutus.Contract.Resumable                (IterationID)

import           Plutus.Contract.Effects.AwaitSlot        (WaitingForSlot)
import           Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..))
import           Plutus.Contract.Effects.ExposeEndpoint   (ActiveEndpoint (..), EndpointDescription (..), EndpointValue)
import           Plutus.Contract.Effects.Instance         (OwnIdRequest)
import           Plutus.Contract.Effects.OwnPubKey        (OwnPubKeyRequest)
import           Plutus.Contract.Effects.UtxoAt           (UtxoAtAddress)

import           Wallet.Effects                           (AddressChangeRequest, AddressChangeResponse)
import           Wallet.Types                             (ContractInstanceId (..))

-- $contract-events
-- The events that compiled Plutus contracts are concerned with. For each type
-- of event there is a request constructor in 'ContractRequest' and a response
-- constructor in 'ContractResponse'.

{- Note [Contract Events]

Each contract instance has two event queues in the PAB: One for the requests
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

data ContractPABRequest =
  AwaitSlotRequest WaitingForSlot -- ^ Wait until a slot number is reached
  | AwaitTxConfirmedRequest TxId -- ^ Wait for a transaction to be confirmed (deeper than k blocks) TODO: confirmation levels
  | UserEndpointRequest ActiveEndpoint -- ^ Expose a named endpoint to the user.
  | OwnPubkeyRequest OwnPubKeyRequest -- ^ Request a public key. It is expected that the wallet treats any outputs locked by this public key as part of its own funds.
  | UtxoAtRequest Address -- ^ Get the unspent transaction outputs at the address.
  | AddressChangedAtRequest AddressChangeRequest -- ^ Wait for the next transaction that modifies the UTXO at the address and return it.
  | WriteTxRequest UnbalancedTx -- ^ Submit an unbalanced transaction to the PAB.
  | OwnInstanceIdRequest OwnIdRequest -- ^ Request the ID of the contract instance.
  deriving  (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | 'ContractPABRequest' with a 'FromJSON' instance that is compatible with
--   the 'ToJSON' instance of 'Plutus.Contract.Schema.Handlers'.
newtype ContractHandlerRequest = ContractHandlerRequest { unContractHandlerRequest :: ContractPABRequest }

instance FromJSON ContractHandlerRequest where
    parseJSON = JSON.withObject "ContractHandlerRequest" $ \v -> ContractHandlerRequest <$> do
        (tag :: Text.Text) <- v .: "tag"
        case tag of
            "slot"            -> AwaitSlotRequest <$> v .: "value"
            "tx-confirmation" -> AwaitTxConfirmedRequest <$> v .: "value"
            "own-pubkey"      -> OwnPubkeyRequest <$> v .: "value"
            "utxo-at"         -> UtxoAtRequest <$> v.: "value"
            "address"         -> AddressChangedAtRequest <$> v .: "value"
            "tx"              -> WriteTxRequest <$> v .: "value"
            "own-instance-id" -> OwnInstanceIdRequest <$> v .: "value"
            _                 -> UserEndpointRequest <$> v .: "value"

instance Pretty ContractPABRequest where
    pretty = \case
        AwaitSlotRequest s        -> "AwaitSlot:" <+> pretty s
        AwaitTxConfirmedRequest t -> "AwaitTxConfirmed:" <+> pretty t
        UserEndpointRequest t     -> "UserEndpoint:" <+> pretty t
        OwnPubkeyRequest r        -> "OwnPubKey:" <+> pretty r
        UtxoAtRequest a           -> "UtxoAt:" <+> pretty a
        AddressChangedAtRequest a -> "AddressChangedAt:" <+> pretty a
        WriteTxRequest u          -> "WriteTx:" <+> pretty u
        OwnInstanceIdRequest r    -> "OwnInstanceId:" <+> pretty r

data ContractPABResponse =
  AwaitSlotResponse Slot
  | AwaitTxConfirmedResponse TxConfirmed
  | UserEndpointResponse EndpointDescription (EndpointValue Value)
  | OwnPubkeyResponse PubKey
  | UtxoAtResponse UtxoAtAddress
  | AddressChangedAtResponse AddressChangeResponse
  | WriteTxResponse W.WriteTxResponse
  | OwnInstanceResponse ContractInstanceId
  deriving  (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

instance Pretty ContractPABResponse where
    pretty = \case
        AwaitSlotResponse s          -> "AwaitSlot:" <+> pretty s
        UserEndpointResponse n r     -> "UserEndpoint:" <+> pretty n <+> pretty r
        OwnPubkeyResponse pk         -> "OwnPubKey:" <+> pretty pk
        UtxoAtResponse utxo          -> "UtxoAt:" <+> pretty utxo
        AddressChangedAtResponse rsp -> "AddressChangedAt:" <+> pretty rsp
        WriteTxResponse w            -> "WriteTx:" <+> pretty w
        AwaitTxConfirmedResponse w   -> "AwaitTxConfirmed:" <+> pretty w
        OwnInstanceResponse r        -> "OwnInstance:" <+> pretty r

-- | 'ContractResponse' with a 'ToJSON' instance that is compatible with
--   the 'FromJSON' instance of 'Plutus.Contract.Schema.Event'.
newtype ContractHandlersResponse = ContractHandlersResponse { unContractHandlersResponse :: ContractPABResponse }

instance ToJSON ContractHandlersResponse where
    toJSON (ContractHandlersResponse c) = case c of
        AwaitSlotResponse s  -> toJSON $ AwaitSlot.event @AwaitSlot.AwaitSlot s
        OwnPubkeyResponse pk -> toJSON $ OwnPubKey.event @OwnPubKey.OwnPubKey pk
        UtxoAtResponse utxo  -> toJSON $ UtxoAt.event @UtxoAt.UtxoAt utxo
        AddressChangedAtResponse rsp -> toJSON $ AddressChangedAt.event @AddressChangedAt.WatchAddress rsp
        WriteTxResponse rsp -> toJSON $ WriteTx.event @WriteTx.WriteTx rsp
        AwaitTxConfirmedResponse (TxConfirmed rsp) -> toJSON $ AwaitTxConfirmed.event @AwaitTxConfirmed.TxConfirmation rsp
        OwnInstanceResponse r -> toJSON $ Instance.event @Instance.OwnId r
        UserEndpointResponse (EndpointDescription n) r -> object ["tag" .= n, "value" .= r]

makePrisms ''ContractPABRequest
makePrisms ''ContractPABResponse
