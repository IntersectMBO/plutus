{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Ledger.Tx
    ( module Export
    -- * ChainIndexTxOut
    , ChainIndexTxOut(..)
    , toTxOut
    , fromTxOut
    -- ** Lenses and Prisms
    , ciTxOutAddress
    , ciTxOutValue
    , ciTxOutDatum
    , ciTxOutValidator
    , _PublicKeyChainIndexTxOut
    , _ScriptChainIndexTxOut
    , SomeCardanoApiTx(..)
    -- * Transactions
    , addSignature
    , pubKeyTxOut
    , scriptTxOut
    , scriptTxOut'
    , updateUtxo
    , txOutRefs
    , unspentOutputsTx
    -- * Hashing transactions
    , txId
    ) where

import qualified Cardano.Api               as C
import           Cardano.Crypto.Hash       (SHA256, digest)
import qualified Codec.CBOR.Write          as Write
import           Codec.Serialise           (Serialise (..))
import           Codec.Serialise.Decoding  (Decoder, decodeBytes, decodeSimple)
import           Codec.Serialise.Encoding  (Encoding (..), Tokens (..))
import           Control.Applicative       ((<|>))
import           Control.Lens              hiding ((.=))
import           Data.Aeson                (FromJSON (parseJSON), ToJSON (toJSON), object, (.:), (.=))
import qualified Data.Aeson                as Aeson
import           Data.Aeson.Types          (Parser, parseFail, prependFailure, typeMismatch)
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Proxy
import qualified Data.Set                  as Set
import           Data.Text.Prettyprint.Doc (Pretty (pretty), braces, colon, hang, nest, viaShow, vsep, (<+>))
import           GHC.Generics              (Generic)
import           Ledger.Address            (pubKeyAddress, scriptAddress)
import           Ledger.Crypto             (PrivateKey, PubKey, signTx, toPublicKey)
import           Ledger.Scripts            (datumHash)
import           Plutus.V1.Ledger.Api      (Credential (PubKeyCredential, ScriptCredential), Datum, DatumHash,
                                            TxId (..), Validator, ValidatorHash, Value, addressCredential, toBuiltin)
import           Plutus.V1.Ledger.Tx       as Export

-- | Transaction output that comes from a chain index query.
--
-- It is defined here instead of the plutus-chain-index because plutus-ledger
-- uses that datatype, and plutus-chain-index can't depend on plutus-ledger
-- because of a cyclic dependency.
--
-- This datatype was created in order to be used in
-- 'Ledger.Constraints.processConstraint', specifically with the constraints
-- 'MustSpendPubKeyOutput' and 'MustSpendScriptOutput'.
data ChainIndexTxOut =
    PublicKeyChainIndexTxOut { _ciTxOutAddress :: Address
                             , _ciTxOutValue   :: Value
                             }
  | ScriptChainIndexTxOut { _ciTxOutAddress   :: Address
                          , _ciTxOutValidator :: Either ValidatorHash Validator
                          , _ciTxOutDatum     :: Either DatumHash Datum
                          , _ciTxOutValue     :: Value
                          }
  deriving (Show, Eq, Serialise, Generic, ToJSON, FromJSON)

makeLenses ''ChainIndexTxOut
makePrisms ''ChainIndexTxOut

-- | Converts a transaction output from the chain index to the plutus-ledger-api
-- transaction output.
--
-- Note that converting from 'ChainIndexTxOut' to 'TxOut' and back to
-- 'ChainIndexTxOut' loses precision ('Datum' and 'Validator' are changed to 'DatumHash' and 'ValidatorHash' respectively)
toTxOut :: ChainIndexTxOut -> TxOut
toTxOut (PublicKeyChainIndexTxOut addr v)          = TxOut addr v Nothing
toTxOut (ScriptChainIndexTxOut addr _ (Left dh) v) = TxOut addr v (Just dh)
toTxOut (ScriptChainIndexTxOut addr _ (Right d) v) = TxOut addr v (Just $ datumHash d)

-- | Converts a plutus-ledger-api transaction output to the chain index
-- transaction output.
fromTxOut :: TxOut -> Maybe ChainIndexTxOut
fromTxOut TxOut { txOutAddress, txOutValue, txOutDatumHash } =
  case addressCredential txOutAddress of
    PubKeyCredential _ -> pure $ PublicKeyChainIndexTxOut txOutAddress txOutValue
    ScriptCredential vh ->
      txOutDatumHash >>= \dh ->
        pure $ ScriptChainIndexTxOut txOutAddress (Left vh) (Left dh) txOutValue

instance Pretty ChainIndexTxOut where
    pretty PublicKeyChainIndexTxOut {_ciTxOutAddress, _ciTxOutValue} =
                hang 2 $ vsep ["-" <+> pretty _ciTxOutValue <+> "addressed to", pretty _ciTxOutAddress]
    pretty ScriptChainIndexTxOut {_ciTxOutAddress, _ciTxOutValue} =
                hang 2 $ vsep ["-" <+> pretty _ciTxOutValue <+> "addressed to", pretty _ciTxOutAddress]

data SomeCardanoApiTx where
  SomeTx :: C.IsCardanoEra era => C.Tx era -> C.EraInMode era C.CardanoMode -> SomeCardanoApiTx

instance Eq SomeCardanoApiTx where
  (SomeTx tx1 C.ByronEraInCardanoMode) == (SomeTx tx2 C.ByronEraInCardanoMode)     = tx1 == tx2
  (SomeTx tx1 C.ShelleyEraInCardanoMode) == (SomeTx tx2 C.ShelleyEraInCardanoMode) = tx1 == tx2
  (SomeTx tx1 C.AllegraEraInCardanoMode) == (SomeTx tx2 C.AllegraEraInCardanoMode) = tx1 == tx2
  (SomeTx tx1 C.MaryEraInCardanoMode) == (SomeTx tx2 C.MaryEraInCardanoMode)       = tx1 == tx2
  (SomeTx tx1 C.AlonzoEraInCardanoMode) == (SomeTx tx2 C.AlonzoEraInCardanoMode)   = tx1 == tx2
  _ == _                                                                           = False

deriving instance Show SomeCardanoApiTx

instance Serialise SomeCardanoApiTx where
  encode (SomeTx tx eraInMode) = encodedMode eraInMode <> Encoding (TkBytes (C.serialiseToCBOR tx))
    where
      encodedMode :: C.EraInMode era C.CardanoMode -> Encoding
      -- 0 and 1 are for ByronEraInByronMode and ShelleyEraInShelleyMode
      encodedMode C.ByronEraInCardanoMode   = Encoding (TkSimple 2)
      encodedMode C.ShelleyEraInCardanoMode = Encoding (TkSimple 3)
      encodedMode C.AllegraEraInCardanoMode = Encoding (TkSimple 4)
      encodedMode C.MaryEraInCardanoMode    = Encoding (TkSimple 5)
      encodedMode C.AlonzoEraInCardanoMode  = Encoding (TkSimple 6)
  decode = do
    w <- decodeSimple
    case w of
      2 -> decodeTx C.AsByronEra C.ByronEraInCardanoMode
      3 -> decodeTx C.AsShelleyEra C.ShelleyEraInCardanoMode
      4 -> decodeTx C.AsAllegraEra C.AllegraEraInCardanoMode
      5 -> decodeTx C.AsMaryEra C.MaryEraInCardanoMode
      6 -> decodeTx C.AsAlonzoEra C.AlonzoEraInCardanoMode
      _ -> fail "Unexpected value while decoding Cardano.Api.EraInMode"
    where
      decodeTx :: C.IsCardanoEra era => C.AsType era -> C.EraInMode era C.CardanoMode -> Decoder s SomeCardanoApiTx
      decodeTx asType eraInMode = do
        bytes <- decodeBytes
        tx <- either (const $ fail "Failed to decode Cardano.Api.Tx") pure $ C.deserialiseFromCBOR (C.AsTx asType) bytes
        pure $ SomeTx tx eraInMode

instance ToJSON SomeCardanoApiTx where
  toJSON (SomeTx tx eraInMode) =
    object [ "tx" .= C.serialiseToTextEnvelope Nothing tx
           , "eraInMode" .= eraInMode
           ]

-- | Converting 'SomeCardanoApiTx' to JSON.
--
-- If the "tx" field is from an unknown era, the JSON parser will print an
-- error at runtime while parsing.
instance FromJSON SomeCardanoApiTx where
  parseJSON v = parseByronInCardanoModeTx v
            <|> parseShelleyEraInCardanoModeTx v
            <|> parseAllegraEraInCardanoModeTx v
            <|> parseMaryEraInCardanoModeTx v
            <|> parseAlonzoEraInCardanoModeTx v
            <|> parseEraInCardanoModeFail v

parseByronInCardanoModeTx :: Aeson.Value -> Parser SomeCardanoApiTx
parseByronInCardanoModeTx =
  parseSomeCardanoTx "Failed to parse ByronEra 'tx' field from SomeCardanoApiTx"
                     (C.AsTx C.AsByronEra)

parseShelleyEraInCardanoModeTx :: Aeson.Value -> Parser SomeCardanoApiTx
parseShelleyEraInCardanoModeTx =
  parseSomeCardanoTx "Failed to parse ShelleyEra 'tx' field from SomeCardanoApiTx"
                     (C.AsTx C.AsShelleyEra)

parseMaryEraInCardanoModeTx :: Aeson.Value -> Parser SomeCardanoApiTx
parseMaryEraInCardanoModeTx =
  parseSomeCardanoTx "Failed to parse MaryEra 'tx' field from SomeCardanoApiTx"
                     (C.AsTx C.AsMaryEra)

parseAllegraEraInCardanoModeTx :: Aeson.Value -> Parser SomeCardanoApiTx
parseAllegraEraInCardanoModeTx =
  parseSomeCardanoTx "Failed to parse AllegraEra 'tx' field from SomeCardanoApiTx"
                     (C.AsTx C.AsAllegraEra)

parseAlonzoEraInCardanoModeTx :: Aeson.Value -> Parser SomeCardanoApiTx
parseAlonzoEraInCardanoModeTx =
  parseSomeCardanoTx "Failed to parse AlonzoEra 'tx' field from SomeCardanoApiTx"
                     (C.AsTx C.AsAlonzoEra)

parseEraInCardanoModeFail :: Aeson.Value -> Parser SomeCardanoApiTx
parseEraInCardanoModeFail _ = fail "Unable to parse 'eraInMode'"

parseSomeCardanoTx
  :: ( FromJSON (C.EraInMode era C.CardanoMode)
     , C.IsCardanoEra era
     )
  => String
  -> C.AsType (C.Tx era)
  -> Aeson.Value
  -> Parser SomeCardanoApiTx
parseSomeCardanoTx errorMsg txAsType (Aeson.Object v) =
  SomeTx
    <$> (v .: "tx" >>= \envelope -> either (const $ parseFail errorMsg)
                                           pure
                                           $ C.deserialiseFromTextEnvelope txAsType envelope)
    <*> v .: "eraInMode"
parseSomeCardanoTx _ _ invalid =
    prependFailure "parsing SomeCardanoApiTx failed, "
      (typeMismatch "Object" invalid)

instance Pretty Tx where
    pretty t@Tx{txInputs, txCollateral, txOutputs, txMint, txFee, txValidRange, txSignatures, txMintScripts, txData} =
        let lines' =
                [ hang 2 (vsep ("inputs:" : fmap pretty (Set.toList txInputs)))
                , hang 2 (vsep ("collateral inputs:" : fmap pretty (Set.toList txCollateral)))
                , hang 2 (vsep ("outputs:" : fmap pretty txOutputs))
                , "mint:" <+> pretty txMint
                , "fee:" <+> pretty txFee
                , hang 2 (vsep ("mps:": fmap pretty (Set.toList txMintScripts)))
                , hang 2 (vsep ("signatures:": fmap (pretty . fst) (Map.toList txSignatures)))
                , "validity range:" <+> viaShow txValidRange
                , hang 2 (vsep ("data:": fmap (pretty . snd) (Map.toList txData) ))
                ]
            txid = txId t
        in nest 2 $ vsep ["Tx" <+> pretty txid <> colon, braces (vsep lines')]

-- | Compute the id of a transaction.
txId :: Tx -> TxId
-- Double hash of a transaction, excluding its witnesses.
txId tx = TxId $ toBuiltin
               $ digest (Proxy @SHA256)
               $ digest (Proxy @SHA256)
               (Write.toStrictByteString $ encode $ strip tx)

-- | Update a map of unspent transaction outputs and signatures based on the inputs
--   and outputs of a transaction.
updateUtxo :: Tx -> Map TxOutRef TxOut -> Map TxOutRef TxOut
updateUtxo tx unspent = (unspent `Map.withoutKeys` spentOutputs tx) `Map.union` unspentOutputsTx tx

-- | A list of a transaction's outputs paired with a 'TxOutRef's referring to them.
txOutRefs :: Tx -> [(TxOut, TxOutRef)]
txOutRefs t = mkOut <$> zip [0..] (txOutputs t) where
    mkOut (i, o) = (o, TxOutRef (txId t) i)

-- | The unspent outputs of a transaction.
unspentOutputsTx :: Tx -> Map TxOutRef TxOut
unspentOutputsTx t = Map.fromList $ fmap f $ zip [0..] $ txOutputs t where
    f (idx, o) = (TxOutRef (txId t) idx, o)

-- | Create a transaction output locked by a validator script hash
--   with the given data script attached.
scriptTxOut' :: Value -> Address -> Datum -> TxOut
scriptTxOut' v a ds = TxOut a v (Just (datumHash ds))

-- | Create a transaction output locked by a validator script and with the given data script attached.
scriptTxOut :: Value -> Validator -> Datum -> TxOut
scriptTxOut v vs = scriptTxOut' v (scriptAddress vs)

-- | Create a transaction output locked by a public key.
pubKeyTxOut :: Value -> PubKey -> TxOut
pubKeyTxOut v pk = TxOut (pubKeyAddress pk) v Nothing

-- | Sign the transaction with a 'PrivateKey' and add the signature to the
--   transaction's list of signatures.
addSignature :: PrivateKey -> Tx -> Tx
addSignature privK tx = tx & signatures . at pubK ?~ sig where
    sig = signTx (txId tx) privK
    pubK = toPublicKey privK

