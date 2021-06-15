{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
module Plutus.Contract.Effects( -- TODO: Move to Requests.Internal
    PABReq(..),
    _AwaitSlotReq,
    _CurrentSlotReq,
    _AwaitTxConfirmedReq,
    _OwnContractInstanceIdReq,
    _SendNotificationReq,
    _OwnPublicKeyReq,
    _UtxoAtReq,
    _AddressChangeReq,
    _WriteTxReq,
    _ExposeEndpointReq,
    PABResp(..),
    _AwaitSlotResp,
    _CurrentSlotResp,
    _AwaitTxConfirmedResp,
    _OwnContractInstanceIdResp,
    _SendNotificationResp,
    _OwnPublicKeyResp,
    _UtxoAtResp,
    _AddressChangeResp,
    _WriteTxResp,
    _ExposeEndpointResp,
    matches,

    -- * Etc.
    UtxoAtAddress(..),
    WriteTxResponse(..),
    writeTxResponse,
    ActiveEndpoint(..),
    TxConfirmed(..)
    ) where

import           Control.Lens                (Iso', iso, makePrisms)
import           Data.Aeson                  (FromJSON, ToJSON)
import qualified Data.Aeson                  as JSON
import qualified Data.Map                    as Map
import           Data.Text.Prettyprint.Doc   (Pretty (..), colon, indent, viaShow, vsep, (<+>))
import           GHC.Generics                (Generic)
import           Ledger                      (Address, PubKey, Tx, TxId, TxOutTx (..), txId)
import           Ledger.AddressMap           (UtxoMap)
import           Ledger.Constraints.OffChain (UnbalancedTx)
import           Ledger.Slot                 (Slot (..))
import           Wallet.API                  (WalletAPIError)
import           Wallet.Types                (AddressChangeRequest, AddressChangeResponse, ContractInstanceId,
                                              EndpointDescription, EndpointValue, Notification, NotificationError)

-- | Requests that 'Contract's can make
data PABReq =
    AwaitSlotReq Slot
    | CurrentSlotReq
    | AwaitTxConfirmedReq TxId
    | OwnContractInstanceIdReq
    | SendNotificationReq Notification -- TODO: Delete
    | OwnPublicKeyReq
    | UtxoAtReq Address
    | AddressChangeReq AddressChangeRequest
    | WriteTxReq UnbalancedTx
    | ExposeEndpointReq ActiveEndpoint
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty PABReq where
  pretty = \case
    AwaitSlotReq s           -> "Await slot:" <+> pretty s
    CurrentSlotReq           -> "Current slot"
    AwaitTxConfirmedReq txid -> "Await tx confirmed:" <+> pretty txid
    OwnContractInstanceIdReq -> "Own contract instance ID"
    SendNotificationReq noti -> "Send notification:" <+> pretty noti
    OwnPublicKeyReq          -> "Own public key"
    UtxoAtReq addr           -> "Utxo at:" <+> pretty addr
    AddressChangeReq req     -> "Address change:" <+> pretty req
    WriteTxReq utx           -> "Write unbalanced tx:" <+> pretty utx
    ExposeEndpointReq ep     -> "Expose endpoint:" <+> pretty ep

-- | Responses that 'Contract's receive
data PABResp =
    AwaitSlotResp Slot
    | CurrentSlotResp Slot
    | AwaitTxConfirmedResp TxId
    | OwnContractInstanceIdResp ContractInstanceId
    | SendNotificationResp (Maybe NotificationError)
    | OwnPublicKeyResp PubKey
    | UtxoAtResp UtxoAtAddress
    | AddressChangeResp AddressChangeResponse
    | WriteTxResp WriteTxResponse
    | ExposeEndpointResp EndpointDescription (EndpointValue JSON.Value)
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)


instance Pretty PABResp where
  pretty = \case
    AwaitSlotResp s             -> "Slot:" <+> pretty s
    CurrentSlotResp s           -> "Current slot:" <+> pretty s
    AwaitTxConfirmedResp txid   -> "Tx confirmed:" <+> pretty txid
    OwnContractInstanceIdResp i -> "Own contract instance ID:" <+> pretty i
    SendNotificationResp e      -> "Send notification:" <+> pretty e
    OwnPublicKeyResp k          -> "Own public key:" <+> pretty k
    UtxoAtResp rsp              -> "Utxo at:" <+> pretty rsp
    AddressChangeResp rsp       -> "Address change:" <+> pretty rsp
    WriteTxResp r               -> "Write unbalanced tx:" <+> pretty r
    ExposeEndpointResp desc rsp -> "Call endpoint" <+> pretty desc <+> "with" <+> pretty rsp

matches :: PABReq -> PABResp -> Bool
matches a b = case (a, b) of
  (AwaitSlotReq{}, AwaitSlotResp{})                       -> True
  (CurrentSlotReq, CurrentSlotResp{})                     -> True
  (AwaitTxConfirmedReq{}, AwaitTxConfirmedResp{})         -> True
  (OwnContractInstanceIdReq, OwnContractInstanceIdResp{}) -> True
  (SendNotificationReq{}, SendNotificationResp{})         -> True
  (OwnPublicKeyReq, OwnPublicKeyResp{})                   -> True
  (UtxoAtReq{}, UtxoAtResp{})                             -> True
  (AddressChangeReq{}, AddressChangeResp{})               -> True
  (WriteTxReq{}, WriteTxResp{})                           -> True
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

data WriteTxResponse =
  WriteTxFailed WalletAPIError
  | WriteTxSuccess Tx
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Pretty WriteTxResponse where
  pretty = \case
    WriteTxFailed e  -> "WriteTxFailed:" <+> pretty e
    WriteTxSuccess i -> "WriteTxSuccess:" <+> pretty (txId i)

writeTxResponse :: Iso' WriteTxResponse (Either WalletAPIError Tx)
writeTxResponse = iso f g where
  f = \case { WriteTxFailed w -> Left w; WriteTxSuccess t -> Right t }
  g = either WriteTxFailed WriteTxSuccess

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

newtype TxConfirmed =
    TxConfirmed { unTxConfirmed :: TxId }
        deriving stock (Eq, Ord, Generic, Show)
        deriving anyclass (ToJSON, FromJSON)
        deriving Pretty via TxId

makePrisms ''PABReq

makePrisms ''PABResp
