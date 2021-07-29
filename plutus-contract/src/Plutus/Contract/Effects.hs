{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Plutus.Contract.Effects( -- TODO: Move to Requests.Internal
    PABReq(..),
    _AwaitSlotReq,
    _AwaitTimeReq,
    _CurrentSlotReq,
    _CurrentTimeReq,
    _AwaitTxStatusChangeReq,
    _OwnContractInstanceIdReq,
    _OwnPublicKeyReq,
    _UtxoAtReq,
    _AddressChangeReq,
    _BalanceTxReq,
    _WriteBalancedTxReq,
    _ExposeEndpointReq,
    PABResp(..),
    _AwaitSlotResp,
    _AwaitTimeResp,
    _CurrentSlotResp,
    _CurrentTimeResp,
    _AwaitTxStatusChangeResp,
    _AwaitTxStatusChangeResp',
    _OwnContractInstanceIdResp,
    _OwnPublicKeyResp,
    _UtxoAtResp,
    _AddressChangeResp,
    _BalanceTxResp,
    _WriteBalancedTxResp,
    _ExposeEndpointResp,
    matches,

    -- * Etc.
    UtxoAtAddress(..),
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
import qualified Data.Map                         as Map
import           Data.Text.Prettyprint.Doc        (Pretty (..), colon, indent, viaShow, vsep, (<+>))
import           Data.Text.Prettyprint.Doc.Extras (PrettyShow (..))
import           GHC.Generics                     (Generic)
import           Ledger                           (Address, OnChainTx, PubKey, Tx, TxId, TxOutTx (..), eitherTx, txId)
import           Ledger.AddressMap                (UtxoMap)
import           Ledger.Constraints.OffChain      (UnbalancedTx)
import           Ledger.Slot                      (Slot (..))
import           Ledger.Time                      (POSIXTime (..))
import           PlutusTx.Lattice                 (MeetSemiLattice (..))
import           Wallet.API                       (WalletAPIError)
import           Wallet.Types                     (AddressChangeRequest, AddressChangeResponse, ContractInstanceId,
                                                   EndpointDescription, EndpointValue)

-- | Requests that 'Contract's can make
data PABReq =
    AwaitSlotReq Slot
    | AwaitTimeReq POSIXTime
    | CurrentSlotReq
    | CurrentTimeReq
    | AwaitTxStatusChangeReq TxId
    | OwnContractInstanceIdReq
    | OwnPublicKeyReq
    | UtxoAtReq Address
    | AddressChangeReq AddressChangeRequest
    | BalanceTxReq UnbalancedTx
    | WriteBalancedTxReq Tx
    | ExposeEndpointReq ActiveEndpoint
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty PABReq where
  pretty = \case
    AwaitSlotReq s              -> "Await slot:" <+> pretty s
    AwaitTimeReq s              -> "Await time:" <+> pretty s
    CurrentSlotReq              -> "Current slot"
    CurrentTimeReq              -> "Current time"
    AwaitTxStatusChangeReq txid -> "Await tx status change:" <+> pretty txid
    OwnContractInstanceIdReq    -> "Own contract instance ID"
    OwnPublicKeyReq             -> "Own public key"
    UtxoAtReq addr              -> "Utxo at:" <+> pretty addr
    AddressChangeReq req        -> "Address change:" <+> pretty req
    BalanceTxReq utx            -> "Balance tx:" <+> pretty utx
    WriteBalancedTxReq tx       -> "Write balanced tx:" <+> pretty tx
    ExposeEndpointReq ep        -> "Expose endpoint:" <+> pretty ep

-- | Responses that 'Contract's receive
data PABResp =
    AwaitSlotResp Slot
    | AwaitTimeResp POSIXTime
    | CurrentSlotResp Slot
    | CurrentTimeResp POSIXTime
    | AwaitTxStatusChangeResp TxId TxStatus
    | OwnContractInstanceIdResp ContractInstanceId
    | OwnPublicKeyResp PubKey
    | UtxoAtResp UtxoAtAddress
    | AddressChangeResp AddressChangeResponse
    | BalanceTxResp BalanceTxResponse
    | WriteBalancedTxResp WriteBalancedTxResponse
    | ExposeEndpointResp EndpointDescription (EndpointValue JSON.Value)
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)


instance Pretty PABResp where
  pretty = \case
    AwaitSlotResp s                     -> "Slot:" <+> pretty s
    AwaitTimeResp s                     -> "Time:" <+> pretty s
    CurrentSlotResp s                   -> "Current slot:" <+> pretty s
    CurrentTimeResp s                   -> "Current time:" <+> pretty s
    AwaitTxStatusChangeResp txid status -> "Status of" <+> pretty txid <+> "changed to" <+> pretty status
    OwnContractInstanceIdResp i         -> "Own contract instance ID:" <+> pretty i
    OwnPublicKeyResp k                  -> "Own public key:" <+> pretty k
    UtxoAtResp rsp                      -> "Utxo at:" <+> pretty rsp
    AddressChangeResp rsp               -> "Address change:" <+> pretty rsp
    BalanceTxResp r                     -> "Balance tx:" <+> pretty r
    WriteBalancedTxResp r               -> "Write balanced tx:" <+> pretty r
    ExposeEndpointResp desc rsp         -> "Call endpoint" <+> pretty desc <+> "with" <+> pretty rsp

matches :: PABReq -> PABResp -> Bool
matches a b = case (a, b) of
  (AwaitSlotReq{}, AwaitSlotResp{})                       -> True
  (AwaitTimeReq{}, AwaitTimeResp{})                       -> True
  (CurrentSlotReq, CurrentSlotResp{})                     -> True
  (CurrentTimeReq, CurrentTimeResp{})                     -> True
  (AwaitTxStatusChangeReq i, AwaitTxStatusChangeResp i' _)         -> i == i'
  (OwnContractInstanceIdReq, OwnContractInstanceIdResp{}) -> True
  (OwnPublicKeyReq, OwnPublicKeyResp{})                   -> True
  (UtxoAtReq{}, UtxoAtResp{})                             -> True
  (AddressChangeReq{}, AddressChangeResp{})               -> True
  (BalanceTxReq{}, BalanceTxResp{})                       -> True
  (WriteBalancedTxReq{}, WriteBalancedTxResp{})           -> True
  (ExposeEndpointReq ActiveEndpoint{aeDescription}, ExposeEndpointResp desc _)
    | aeDescription == desc -> True
  _                                                       -> False

data UtxoAtAddress =
    UtxoAtAddress
        { address :: Address
        , utxo    :: UtxoMap
        }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty UtxoAtAddress where
  pretty UtxoAtAddress{address, utxo} =
    let
      prettyTxOutPair (txoutref, TxOutTx{txOutTxOut}) =
        pretty txoutref <> colon <+> pretty txOutTxOut
      utxos = vsep $ fmap prettyTxOutPair (Map.toList utxo)
    in vsep ["Utxo at" <+> pretty address <+> "=", indent 2 utxos]

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
