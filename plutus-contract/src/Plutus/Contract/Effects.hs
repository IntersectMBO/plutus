{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Plutus.Contract.Effects( -- TODO: Move to Requests.Internal
    -- * Plutus application backend request effect types
    PABReq(..),
    _AwaitSlotReq,
    _AwaitTimeReq,
    _AwaitUtxoSpentReq,
    _AwaitUtxoProducedReq,
    _CurrentSlotReq,
    _CurrentTimeReq,
    _AwaitTxStatusChangeReq,
    _OwnContractInstanceIdReq,
    _OwnPublicKeyReq,
    _ChainIndexQueryReq,
    _BalanceTxReq,
    _WriteBalancedTxReq,
    _ExposeEndpointReq,
    _PosixTimeRangeToContainedSlotRangeReq,
    -- ** Chain index query effect types
    _DatumFromHash,
    _ValidatorFromHash,
    _MintingPolicyFromHash,
    _TxOutFromRef,
    _TxFromTxId,
    _UtxoSetMembership,
    _UtxoSetAtAddress,
    _GetTip,
    -- * Plutus application backend response effect types
    PABResp(..),
    _AwaitSlotResp,
    _AwaitTimeResp,
    _AwaitUtxoSpentResp,
    _AwaitUtxoProducedResp,
    _CurrentSlotResp,
    _CurrentTimeResp,
    _AwaitTxStatusChangeResp,
    _AwaitTxStatusChangeResp',
    _OwnContractInstanceIdResp,
    _OwnPublicKeyResp,
    _ChainIndexQueryResp,
    _BalanceTxResp,
    _WriteBalancedTxResp,
    _ExposeEndpointResp,
    _PosixTimeRangeToContainedSlotRangeResp,
    -- ** Chain index response effect types
    _DatumHashResponse,
    _ValidatorHashResponse,
    _MintingPolicyHashResponse,
    _TxOutRefResponse,
    _TxIdResponse,
    _UtxoSetMembershipResponse,
    _UtxoSetAtResponse,
    _GetTipResponse,
    -- * Etc.
    matches,
    ChainIndexQuery(..),
    ChainIndexResponse(..),
    BalanceTxResponse(..),
    balanceTxResponse,
    WriteBalancedTxResponse(..),
    writeBalancedTxResponse,
    ActiveEndpoint(..),
    TxValidity(..),
    TxStatus(..),
    Depth(..),
    isConfirmed,
    increaseDepth,
    initialStatus
    ) where

import           Control.Lens                     (Iso', Prism', iso, makePrisms, prism')
import           Data.Aeson                       (FromJSON, ToJSON)
import qualified Data.Aeson                       as JSON
import           Data.List.NonEmpty               (NonEmpty)
import           Data.Text.Prettyprint.Doc        (Pretty (..), hsep, indent, viaShow, vsep, (<+>))
import           Data.Text.Prettyprint.Doc.Extras (PrettyShow (..))
import           GHC.Generics                     (Generic)
import           Ledger                           (Address, Datum, DatumHash, MintingPolicy, MintingPolicyHash,
                                                   OnChainTx, PubKey, StakeValidator, StakeValidatorHash, Tx, TxId,
                                                   TxOutRef, ValidatorHash, eitherTx, txId)
import           Ledger.Constraints.OffChain      (UnbalancedTx)
import           Ledger.Credential                (Credential)
import           Ledger.Scripts                   (Validator)
import           Ledger.Slot                      (Slot (..), SlotRange)
import           Ledger.Time                      (POSIXTime (..), POSIXTimeRange)
import           Ledger.TimeSlot                  (SlotConversionError)
import           Ledger.Tx                        (ChainIndexTxOut)
import           Plutus.ChainIndex                (Tip)
import           Plutus.ChainIndex.Tx             (ChainIndexTx (_citxTxId))
import           Plutus.ChainIndex.Types          (Page (pageItems))
import           PlutusTx.Lattice                 (MeetSemiLattice (..))
import           Wallet.API                       (WalletAPIError)
import           Wallet.Types                     (ContractInstanceId, EndpointDescription, EndpointValue)

-- | Requests that 'Contract's can make
data PABReq =
    AwaitSlotReq Slot
    | AwaitTimeReq POSIXTime
    | AwaitUtxoSpentReq TxOutRef
    | AwaitUtxoProducedReq Address
    | AwaitTxStatusChangeReq TxId
    | CurrentSlotReq
    | CurrentTimeReq
    | OwnContractInstanceIdReq
    | OwnPublicKeyReq
    | ChainIndexQueryReq ChainIndexQuery
    | BalanceTxReq UnbalancedTx
    | WriteBalancedTxReq Tx
    | ExposeEndpointReq ActiveEndpoint
    | PosixTimeRangeToContainedSlotRangeReq POSIXTimeRange
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty PABReq where
  pretty = \case
    AwaitSlotReq s                          -> "Await slot:" <+> pretty s
    AwaitTimeReq s                          -> "Await time:" <+> pretty s
    AwaitUtxoSpentReq utxo                  -> "Await utxo spent:" <+> pretty utxo
    AwaitUtxoProducedReq a                  -> "Await utxo produced:" <+> pretty a
    CurrentSlotReq                          -> "Current slot"
    CurrentTimeReq                          -> "Current time"
    AwaitTxStatusChangeReq txid             -> "Await tx status change:" <+> pretty txid
    OwnContractInstanceIdReq                -> "Own contract instance ID"
    OwnPublicKeyReq                         -> "Own public key"
    ChainIndexQueryReq q                    -> "Chain index query:" <+> pretty q
    BalanceTxReq utx                        -> "Balance tx:" <+> pretty utx
    WriteBalancedTxReq tx                   -> "Write balanced tx:" <+> pretty tx
    ExposeEndpointReq ep                    -> "Expose endpoint:" <+> pretty ep
    PosixTimeRangeToContainedSlotRangeReq r -> "Posix time range to contained slot range:" <+> pretty r

-- | Responses that 'Contract's receive
data PABResp =
    AwaitSlotResp Slot
    | AwaitTimeResp POSIXTime
    | AwaitUtxoSpentResp ChainIndexTx
    | AwaitUtxoProducedResp (NonEmpty ChainIndexTx)
    | AwaitTxStatusChangeResp TxId TxStatus
    | CurrentSlotResp Slot
    | CurrentTimeResp POSIXTime
    | OwnContractInstanceIdResp ContractInstanceId
    | OwnPublicKeyResp PubKey
    | ChainIndexQueryResp ChainIndexResponse
    | BalanceTxResp BalanceTxResponse
    | WriteBalancedTxResp WriteBalancedTxResponse
    | ExposeEndpointResp EndpointDescription (EndpointValue JSON.Value)
    | PosixTimeRangeToContainedSlotRangeResp (Either SlotConversionError SlotRange)
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty PABResp where
  pretty = \case
    AwaitSlotResp s                          -> "Slot:" <+> pretty s
    AwaitTimeResp s                          -> "Time:" <+> pretty s
    AwaitUtxoSpentResp utxo                  -> "Utxo spent:" <+> pretty utxo
    AwaitUtxoProducedResp addr               -> "Utxo produced:" <+> pretty addr
    CurrentSlotResp s                        -> "Current slot:" <+> pretty s
    CurrentTimeResp s                        -> "Current time:" <+> pretty s
    AwaitTxStatusChangeResp txid status      -> "Status of" <+> pretty txid <+> "changed to" <+> pretty status
    OwnContractInstanceIdResp i              -> "Own contract instance ID:" <+> pretty i
    OwnPublicKeyResp k                       -> "Own public key:" <+> pretty k
    ChainIndexQueryResp rsp                  -> pretty rsp
    BalanceTxResp r                          -> "Balance tx:" <+> pretty r
    WriteBalancedTxResp r                    -> "Write balanced tx:" <+> pretty r
    ExposeEndpointResp desc rsp              -> "Call endpoint" <+> pretty desc <+> "with" <+> pretty rsp
    PosixTimeRangeToContainedSlotRangeResp r -> "Slot range:" <+> pretty r

matches :: PABReq -> PABResp -> Bool
matches a b = case (a, b) of
  (AwaitSlotReq{}, AwaitSlotResp{})                        -> True
  (AwaitTimeReq{}, AwaitTimeResp{})                        -> True
  (AwaitUtxoSpentReq{}, AwaitUtxoSpentResp{})              -> True
  (AwaitUtxoProducedReq{}, AwaitUtxoProducedResp{})        -> True
  (CurrentSlotReq, CurrentSlotResp{})                      -> True
  (CurrentTimeReq, CurrentTimeResp{})                      -> True
  (AwaitTxStatusChangeReq i, AwaitTxStatusChangeResp i' _) -> i == i'
  (OwnContractInstanceIdReq, OwnContractInstanceIdResp{})  -> True
  (OwnPublicKeyReq, OwnPublicKeyResp{})                    -> True
  (ChainIndexQueryReq r, ChainIndexQueryResp r')           -> chainIndexMatches r r'
  (BalanceTxReq{}, BalanceTxResp{})                        -> True
  (WriteBalancedTxReq{}, WriteBalancedTxResp{})            -> True
  (ExposeEndpointReq ActiveEndpoint{aeDescription}, ExposeEndpointResp desc _)
    | aeDescription == desc -> True
  (PosixTimeRangeToContainedSlotRangeReq{}, PosixTimeRangeToContainedSlotRangeResp{}) -> True
  _                                                        -> False

chainIndexMatches :: ChainIndexQuery -> ChainIndexResponse -> Bool
chainIndexMatches q r = case (q, r) of
    (DatumFromHash{}, DatumHashResponse{})                   -> True
    (ValidatorFromHash{}, ValidatorHashResponse{})           -> True
    (MintingPolicyFromHash{}, MintingPolicyHashResponse{})   -> True
    (StakeValidatorFromHash{}, StakeValidatorHashResponse{}) -> True
    (TxOutFromRef{}, TxOutRefResponse{})                     -> True
    (TxFromTxId{}, TxIdResponse{})                           -> True
    (UtxoSetMembership{}, UtxoSetMembershipResponse{})       -> True
    (UtxoSetAtAddress{}, UtxoSetAtResponse{})                -> True
    (GetTip{}, GetTipResponse{})                             -> True
    _                                                        -> False

-- | Represents all possible chain index queries. Each constructor contains the
-- input(s) needed for the query. These possible queries correspond to the
-- constructors of the data type 'Plutus.ChainIndex.Effects.ChainIndexQueryEffect'.
data ChainIndexQuery =
    DatumFromHash DatumHash
  | ValidatorFromHash ValidatorHash
  | MintingPolicyFromHash MintingPolicyHash
  | StakeValidatorFromHash StakeValidatorHash
  | TxOutFromRef TxOutRef
  | TxFromTxId TxId
  | UtxoSetMembership TxOutRef
  | UtxoSetAtAddress Credential
  | GetTip
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty ChainIndexQuery where
    pretty = \case
        DatumFromHash h            -> "requesting datum from hash" <+> pretty h
        ValidatorFromHash h        -> "requesting validator from hash" <+> pretty h
        MintingPolicyFromHash h    -> "requesting minting policy from hash" <+> pretty h
        StakeValidatorFromHash h   -> "requesting stake validator from hash" <+> pretty h
        TxOutFromRef r             -> "requesting utxo from utxo reference" <+> pretty r
        TxFromTxId i               -> "requesting chain index tx from id" <+> pretty i
        UtxoSetMembership txOutRef -> "whether tx output is part of the utxo set" <+> pretty txOutRef
        UtxoSetAtAddress c         -> "requesting utxos located at addresses with the credential" <+> pretty c
        GetTip                     -> "requesting the tip of the chain index"

-- | Represents all possible responses to chain index queries. Each constructor
-- contain the output resulting for the chain index query. These possible
-- responses come from the data type 'Plutus.ChainIndex.Effects.ChainIndexQueryEffect'.
data ChainIndexResponse =
    DatumHashResponse (Maybe Datum)
  | ValidatorHashResponse (Maybe Validator)
  | MintingPolicyHashResponse (Maybe MintingPolicy)
  | StakeValidatorHashResponse (Maybe StakeValidator)
  | TxOutRefResponse (Maybe ChainIndexTxOut)
  | TxIdResponse (Maybe ChainIndexTx)
  | UtxoSetMembershipResponse (Tip, Bool)
  | UtxoSetAtResponse (Tip, Page TxOutRef)
  | GetTipResponse Tip
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty ChainIndexResponse where
    pretty = \case
        DatumHashResponse d -> "Chain index datum from hash response:" <+> pretty d
        ValidatorHashResponse v -> "Chain index validator from hash response:" <+> pretty v
        MintingPolicyHashResponse m -> "Chain index minting policy from hash response:" <+> pretty m
        StakeValidatorHashResponse m -> "Chain index stake validator from hash response:" <+> pretty m
        TxOutRefResponse t -> "Chain index utxo from utxo ref response:" <+> pretty t
        TxIdResponse t -> "Chain index tx from tx id response:" <+> pretty (_citxTxId <$> t)
        UtxoSetMembershipResponse (tip, b) ->
                "Chain index response whether tx output ref is part of the UTxO set:"
            <+> pretty b
            <+> "with tip"
            <+> pretty tip
        UtxoSetAtResponse (tip, txOutRefPage) ->
                "Chain index UTxO set from address response:"
            <+> "Current tip is"
            <+> pretty tip
            <+> "and utxo refs are"
            <+> hsep (fmap pretty $ pageItems txOutRefPage)
        GetTipResponse tip -> "Chain index get tip response:" <+> pretty tip

-- | Validity of a transaction that has been added to the ledger
data TxValidity = TxValid | TxInvalid | UnknownValidity
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving Pretty via (PrettyShow TxValidity)

instance MeetSemiLattice TxValidity where
  TxValid /\ TxValid     = TxValid
  TxInvalid /\ TxInvalid = TxInvalid
  _ /\ _                 = UnknownValidity

{- Note [TxStatus state machine]

The status of a transaction is described by the following state machine.

Current state | Next state(s)
-----------------------------------------------------
Unknown       | OnChain
OnChain       | OnChain, Unknown, Committed
Committed     | -

The initial state after submitting the transaction is Unknown.

-}

-- | How many blocks deep the tx is on the chain
newtype Depth = Depth Int
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (Num, Real, Enum, Integral, Pretty, ToJSON, FromJSON)

instance MeetSemiLattice Depth where
  Depth a /\ Depth b = Depth (max a b)

-- | The status of a Cardano transaction
data TxStatus =
  Unknown -- ^ The transaction is not on the chain. That's all we can say.
  | TentativelyConfirmed Depth TxValidity -- ^ The transaction is on the chain, n blocks deep. It can still be rolled back.
  | Committed TxValidity -- ^ The transaction is on the chain. It cannot be rolled back anymore.
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving Pretty via (PrettyShow TxStatus)

instance MeetSemiLattice TxStatus where
  Unknown /\ a                                             = a
  a /\ Unknown                                             = a
  TentativelyConfirmed d1 v1 /\ TentativelyConfirmed d2 v2 = TentativelyConfirmed (d1 /\ d2) (v1 /\ v2)
  TentativelyConfirmed _ v1 /\ Committed v2                = Committed (v1 /\ v2)
  Committed v1 /\ TentativelyConfirmed _ v2                = Committed (v1 /\ v2)
  Committed v1 /\ Committed v2                             = Committed (v1 /\ v2)

-- | The 'TxStatus' of a transaction right after it was added to the chain
initialStatus :: OnChainTx -> TxStatus
initialStatus =
  TentativelyConfirmed 0 . eitherTx (const TxInvalid) (const TxValid)

-- | Whether a 'TxStatus' counts as confirmed given the minimum depth
isConfirmed :: Depth -> TxStatus -> Bool
isConfirmed minDepth = \case
    TentativelyConfirmed d _ | d >= minDepth -> True
    Committed{}                              -> True
    _                                        -> False

-- | Increase the depth of a tentatively confirmed transaction
increaseDepth :: TxStatus -> TxStatus
increaseDepth (TentativelyConfirmed d s)
  | d < succ chainConstant = TentativelyConfirmed (d + 1) s
  | otherwise              = Committed s
increaseDepth e                        = e

-- TODO: Configurable!
-- | The depth (in blocks) after which a transaction cannot be rolled back anymore
chainConstant :: Depth
chainConstant = Depth 8

data BalanceTxResponse =
  BalanceTxFailed WalletAPIError
  | BalanceTxSuccess Tx
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Pretty BalanceTxResponse where
  pretty = \case
    BalanceTxFailed e  -> "BalanceTxFailed:" <+> pretty e
    BalanceTxSuccess i -> "BalanceTxSuccess:" <+> pretty (txId i)

_AwaitTxStatusChangeResp' :: TxId -> Prism' PABResp TxStatus
_AwaitTxStatusChangeResp' i =
  prism'
    (AwaitTxStatusChangeResp i)
    (\case { AwaitTxStatusChangeResp i' s | i == i' -> Just s; _ -> Nothing })

balanceTxResponse :: Iso' BalanceTxResponse (Either WalletAPIError Tx)
balanceTxResponse = iso f g where
  f = \case { BalanceTxFailed w -> Left w; BalanceTxSuccess t -> Right t }
  g = either BalanceTxFailed BalanceTxSuccess

data WriteBalancedTxResponse =
  WriteBalancedTxFailed WalletAPIError
  | WriteBalancedTxSuccess Tx
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Pretty WriteBalancedTxResponse where
  pretty = \case
    WriteBalancedTxFailed e  -> "WriteBalancedTxFailed:" <+> pretty e
    WriteBalancedTxSuccess i -> "WriteBalancedTxSuccess:" <+> pretty (txId i)

writeBalancedTxResponse :: Iso' WriteBalancedTxResponse (Either WalletAPIError Tx)
writeBalancedTxResponse = iso f g where
  f = \case { WriteBalancedTxFailed w -> Left w; WriteBalancedTxSuccess t -> Right t }
  g = either WriteBalancedTxFailed WriteBalancedTxSuccess

data ActiveEndpoint = ActiveEndpoint
  { aeDescription :: EndpointDescription -- ^ The name of the endpoint
  , aeMetadata    :: Maybe JSON.Value -- ^ Data that should be shown to the user
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Pretty ActiveEndpoint where
  pretty ActiveEndpoint{aeDescription, aeMetadata} =
    indent 2 $ vsep
      [ "Endpoint:" <+> pretty aeDescription
      , "Metadata:" <+> viaShow aeMetadata
      ]

makePrisms ''PABReq

makePrisms ''PABResp

makePrisms ''ChainIndexQuery

makePrisms ''ChainIndexResponse
