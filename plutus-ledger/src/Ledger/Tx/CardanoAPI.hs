{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedLists    #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ViewPatterns       #-}

{-# OPTIONS_GHC -Wno-orphans        #-}

{-|

Interface to the transaction types from 'cardano-api'

-}
module Ledger.Tx.CardanoAPI(
  SomeCardanoApiTx(..)
  , txOutRefs
  , unspentOutputsTx
  , fromCardanoTxId
  , fromCardanoTxIn
  , fromCardanoTxInsCollateral
  , fromCardanoTxInWitness
  , fromCardanoTxOut
  , fromCardanoAddress
  , fromCardanoMintValue
  , fromCardanoValue
  , fromCardanoFee
  , fromCardanoValidityRange
  , fromCardanoExtraScriptData
  , fromCardanoScriptInEra
  , fromCardanoScriptData
  , fromTxScriptValidity
  , scriptDataFromCardanoTxBody
  , plutusScriptsFromTxBody
  , toCardanoTxBody
  , toCardanoTxIn
  , toCardanoTxInsCollateral
  , toCardanoTxInWitness
  , toCardanoTxOut
  , toCardanoAddress
  , toCardanoMintValue
  , toCardanoValue
  , toCardanoFee
  , toCardanoValidityRange
  , toCardanoExtraScriptData
  , toCardanoScriptInEra
  , toCardanoPaymentKeyHash
  , toCardanoScriptHash
  , ToCardanoError(..)
  , FromCardanoError(..)
) where

import qualified Cardano.Api                     as C
import qualified Cardano.Api.Byron               as C
import qualified Cardano.Api.Shelley             as C
import           Cardano.BM.Data.Tracer          (ToObject (..))
import           Cardano.Chain.Common            (addrToBase58)
import qualified Cardano.Ledger.Alonzo.Scripts   as Alonzo
import qualified Cardano.Ledger.Alonzo.TxWitness as C
import qualified Cardano.Ledger.Core             as Ledger
import           Codec.Serialise                 (Serialise, deserialiseOrFail)
import qualified Codec.Serialise                 as Codec
import           Codec.Serialise.Decoding        (Decoder, decodeBytes, decodeSimple)
import           Codec.Serialise.Encoding        (Encoding (..), Tokens (..))
import           Control.Applicative             ((<|>))
import           Control.Lens                    hiding ((.=))
import           Control.Monad                   (when)
import           Data.Aeson                      (FromJSON (parseJSON), ToJSON (toJSON), object, (.:), (.=))
import qualified Data.Aeson                      as Aeson
import           Data.Aeson.Types                (Parser, parseFail, prependFailure, typeMismatch)
import           Data.Bifunctor                  (first)
import           Data.ByteString                 (ByteString)
import qualified Data.ByteString                 as BS
import qualified Data.ByteString.Lazy            as BSL
import qualified Data.ByteString.Short           as SBS
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import           Data.Maybe                      (mapMaybe)
import           Data.OpenApi                    (NamedSchema (..), OpenApiType (..), byteSchema, declareSchemaRef,
                                                  properties, required, sketchSchema, type_)
import qualified Data.OpenApi                    as OpenApi
import           Data.Proxy                      (Proxy (Proxy))
import qualified Data.Set                        as Set
import           Data.Tuple                      (swap)
import           Data.Typeable                   (Typeable)
import           GHC.Generics                    (Generic)
import qualified Ledger.Scripts                  as P
import           Ledger.Tx.CardanoAPITemp        (makeTransactionBody')
import qualified Plutus.V1.Ledger.Ada            as Ada
import qualified Plutus.V1.Ledger.Api            as Api
import qualified Plutus.V1.Ledger.Api            as P
import qualified Plutus.V1.Ledger.Credential     as Credential
import qualified Plutus.V1.Ledger.Slot           as P
import qualified Plutus.V1.Ledger.Tx             as P
import qualified Plutus.V1.Ledger.Value          as Value
import qualified PlutusTx.Prelude                as PlutusTx
import           Prettyprinter                   (Pretty (..), colon, viaShow, (<+>))

instance (Typeable era, Typeable mode) => OpenApi.ToSchema (C.EraInMode era mode) where
  declareNamedSchema _ = do
    return $ NamedSchema (Just "EraInMode") $ sketchSchema C.AlonzoEraInCardanoMode

instance (Typeable era) => OpenApi.ToSchema (C.Tx era) where
  declareNamedSchema _ = do
    return $ NamedSchema (Just "Tx") byteSchema

-- | Cardano tx from any era.
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

instance Pretty SomeCardanoApiTx where
  pretty = viaShow

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

instance OpenApi.ToSchema SomeCardanoApiTx where
  declareNamedSchema _ = do
    txSchema <- declareSchemaRef (Proxy :: Proxy (C.Tx C.AlonzoEra))
    eraInModeSchema <- declareSchemaRef (Proxy :: Proxy (C.EraInMode C.AlonzoEra C.CardanoMode))
    return $ NamedSchema (Just "SomeCardanoApiTx") $ mempty
      & type_ ?~ OpenApiObject
      & properties .~
          [ ("tx", txSchema)
          , ("eraInMode", eraInModeSchema)
          ]
      & required .~ [ "tx", "eraInMode" ]

txOutRefs :: SomeCardanoApiTx -> [(P.TxOut, P.TxOutRef)]
txOutRefs (SomeTx (C.Tx txBody@(C.TxBody C.TxBodyContent{..}) _) _) =
  mkOut <$> zip [0..] plutusTxOuts
  where
    mkOut (i, o) = (o, P.TxOutRef (fromCardanoTxId $ C.getTxId txBody) i)
    plutusTxOuts = mapMaybe (either (const Nothing) Just . fromCardanoTxOut) txOuts

unspentOutputsTx :: SomeCardanoApiTx -> Map P.TxOutRef P.TxOut
unspentOutputsTx tx = Map.fromList $ swap <$> txOutRefs tx

-- | Given a 'C.TxScriptValidity era', if the @era@ supports scripts, return a
-- @True@ or @False@ depending on script validity. If the @era@ does not support
-- scripts, always return @True@.
fromTxScriptValidity :: C.TxScriptValidity era -> Bool
fromTxScriptValidity C.TxScriptValidityNone                                                      = True
fromTxScriptValidity (C.TxScriptValidity C.TxScriptValiditySupportedInAlonzoEra C.ScriptValid)   = True
fromTxScriptValidity (C.TxScriptValidity C.TxScriptValiditySupportedInAlonzoEra C.ScriptInvalid) = False

-- | Given a 'C.TxBody from a 'C.Tx era', return the datums and redeemers along
-- with their hashes.
scriptDataFromCardanoTxBody
  :: C.TxBody era
  -> (Map P.DatumHash P.Datum, Map P.RedeemerHash P.Redeemer)
scriptDataFromCardanoTxBody C.ByronTxBody {} = (mempty, mempty)
scriptDataFromCardanoTxBody (C.ShelleyTxBody _ _ _ C.TxBodyNoScriptData _ _) =
  (mempty, mempty)
scriptDataFromCardanoTxBody
  (C.ShelleyTxBody _ _ _ (C.TxBodyScriptData _ (C.TxDats' dats) (C.Redeemers' reds)) _ _) =

  let datums = Map.fromList
             $ fmap ( (\d -> (P.datumHash d, d))
                    . P.Datum
                    . fromCardanoScriptData
                    . C.fromAlonzoData
                    )
             $ Map.elems dats
      redeemers = Map.fromList
                $ fmap ( (\r -> (P.redeemerHash r, r))
                       . P.Redeemer
                       . fromCardanoScriptData
                       . C.fromAlonzoData
                       . fst
                       )
                $ Map.elems reds
   in (datums, redeemers)

-- | Extract plutus scripts from a Cardano API tx body.
--
-- Note that Plutus scripts are only supported in Alonzo era and onwards.
plutusScriptsFromTxBody :: C.TxBody era -> Map P.ScriptHash P.Script
plutusScriptsFromTxBody C.ByronTxBody {} = mempty
plutusScriptsFromTxBody (C.ShelleyTxBody shelleyBasedEra _ scripts _ _ _) =
  Map.fromList $ mapMaybe (fromLedgerScript shelleyBasedEra) scripts

-- | Convert a script from a Cardano api in shelley based era to a Plutus script along with it's hash.
--
-- Note that Plutus scripts are only supported in Alonzo era and onwards.
fromLedgerScript
  :: C.ShelleyBasedEra era
  -> Ledger.Script (C.ShelleyLedgerEra era)
  -> Maybe (P.ScriptHash, P.Script)
fromLedgerScript C.ShelleyBasedEraShelley _     = Nothing
fromLedgerScript C.ShelleyBasedEraAllegra _     = Nothing
fromLedgerScript C.ShelleyBasedEraMary _        = Nothing
fromLedgerScript C.ShelleyBasedEraAlonzo script = fromAlonzoLedgerScript script

-- | Convert a script the Alonzo era to a Plutus script along with it's hash.
fromAlonzoLedgerScript :: Alonzo.Script a -> Maybe (P.ScriptHash, P.Script)
fromAlonzoLedgerScript Alonzo.TimelockScript {} = Nothing
fromAlonzoLedgerScript (Alonzo.PlutusScript bs) =
  let script = fmap (\s -> (P.scriptHash s, s))
             $ deserialiseOrFail
             $ BSL.fromStrict
             $ SBS.fromShort bs
   in either (const Nothing) Just script

toCardanoTxBody ::
    [Api.PubKeyHash] -- ^ Required signers of the transaction
    -> Maybe C.ProtocolParameters -- ^ Protocol parameters to use. Building Plutus transactions will fail if this is 'Nothing'
    -> C.NetworkId -- ^ Network ID
    -> P.Tx
    -> Either ToCardanoError (C.TxBody C.AlonzoEra)
toCardanoTxBody sigs protocolParams networkId P.Tx{..} = do
    txIns <- traverse toCardanoTxInBuild $ Set.toList txInputs
    txInsCollateral <- toCardanoTxInsCollateral txCollateral
    txOuts <- traverse (toCardanoTxOut networkId) txOutputs
    txFee' <- toCardanoFee txFee
    txValidityRange <- toCardanoValidityRange txValidRange
    txMintValue <- toCardanoMintValue txRedeemers txMint txMintScripts
    txExtraKeyWits <- C.TxExtraKeyWitnesses C.ExtraKeyWitnessesInAlonzoEra <$> traverse toCardanoPaymentKeyHash sigs
    first TxBodyError $ makeTransactionBody' C.TxBodyContent
        { txIns = txIns
        , txInsCollateral = txInsCollateral
        , txOuts = txOuts
        , txFee = txFee'
        , txValidityRange = txValidityRange
        , txExtraScriptData = C.BuildTxWith $ toCardanoExtraScriptData (Map.elems txData)
        , txMintValue = txMintValue
        , txProtocolParams = C.BuildTxWith protocolParams
        , txScriptValidity = C.TxScriptValidityNone
        , txExtraKeyWits
        -- unused:
        , txMetadata = C.TxMetadataNone
        , txAuxScripts = C.TxAuxScriptsNone
        , txWithdrawals = C.TxWithdrawalsNone
        , txCertificates = C.TxCertificatesNone
        , txUpdateProposal = C.TxUpdateProposalNone
        }

fromCardanoTxIn :: C.TxIn -> P.TxOutRef
fromCardanoTxIn (C.TxIn txId (C.TxIx txIx)) = P.TxOutRef (fromCardanoTxId txId) (toInteger txIx)

toCardanoTxInBuild :: P.TxIn -> Either ToCardanoError (C.TxIn, C.BuildTxWith C.BuildTx (C.Witness C.WitCtxTxIn C.AlonzoEra))
toCardanoTxInBuild (P.TxIn txInRef (Just txInType)) = (,) <$> toCardanoTxIn txInRef <*> (C.BuildTxWith <$> toCardanoTxInWitness txInType)
toCardanoTxInBuild (P.TxIn _ Nothing) = Left MissingTxInType

toCardanoTxIn :: P.TxOutRef -> Either ToCardanoError C.TxIn
toCardanoTxIn (P.TxOutRef txId txIx) = C.TxIn <$> toCardanoTxId txId <*> pure (C.TxIx (fromInteger txIx))

fromCardanoTxId :: C.TxId -> P.TxId
fromCardanoTxId txId = P.TxId $ PlutusTx.toBuiltin $ C.serialiseToRawBytes txId

toCardanoTxId :: P.TxId -> Either ToCardanoError C.TxId
toCardanoTxId (P.TxId bs) =
    tag "toCardanoTxId"
    $ deserialiseFromRawBytes C.AsTxId $ PlutusTx.fromBuiltin bs

fromCardanoTxInsCollateral :: C.TxInsCollateral era -> Set.Set P.TxIn
fromCardanoTxInsCollateral C.TxInsCollateralNone       = mempty
fromCardanoTxInsCollateral (C.TxInsCollateral _ txIns) = Set.fromList $ fmap (P.pubKeyTxIn . fromCardanoTxIn) txIns

toCardanoTxInsCollateral :: Set.Set P.TxIn -> Either ToCardanoError (C.TxInsCollateral C.AlonzoEra)
toCardanoTxInsCollateral = fmap (C.TxInsCollateral C.CollateralInAlonzoEra) . traverse (toCardanoTxIn . P.txInRef) . Set.toList

fromCardanoTxInWitness :: C.Witness C.WitCtxTxIn era -> Either FromCardanoError P.TxInType
fromCardanoTxInWitness (C.KeyWitness C.KeyWitnessForSpending) = pure P.ConsumePublicKeyAddress
fromCardanoTxInWitness
    (C.ScriptWitness _
        (C.PlutusScriptWitness C.PlutusScriptV1InAlonzo C.PlutusScriptV1
            script
            (C.ScriptDatumForTxIn datum)
            redeemer
            _))
    = pure $ P.ConsumeScriptAddress
        (P.Validator $ fromCardanoPlutusScript script)
        (P.Redeemer $ fromCardanoScriptData redeemer)
        (P.Datum $ fromCardanoScriptData datum)
fromCardanoTxInWitness (C.ScriptWitness _ C.SimpleScriptWitness{}) = pure P.ConsumeSimpleScriptAddress

toCardanoTxInWitness :: P.TxInType -> Either ToCardanoError (C.Witness C.WitCtxTxIn C.AlonzoEra)
toCardanoTxInWitness P.ConsumePublicKeyAddress = pure (C.KeyWitness C.KeyWitnessForSpending)
toCardanoTxInWitness P.ConsumeSimpleScriptAddress = Left SimpleScriptsNotSupportedToCardano -- TODO: Better support for simple scripts
toCardanoTxInWitness
    (P.ConsumeScriptAddress
        (P.Validator validator)
        (P.Redeemer redeemer)
        (P.Datum datum))
    = C.ScriptWitness C.ScriptWitnessForSpending <$>
        (C.PlutusScriptWitness C.PlutusScriptV1InAlonzo C.PlutusScriptV1
        <$> toCardanoPlutusScript validator
        <*> pure (C.ScriptDatumForTxIn $ toCardanoScriptData datum)
        <*> pure (toCardanoScriptData redeemer)
        <*> pure zeroExecutionUnits
        )

toCardanoMintWitness :: P.Redeemers -> Int -> P.MintingPolicy -> Either ToCardanoError (C.ScriptWitness C.WitCtxMint C.AlonzoEra)
toCardanoMintWitness redeemers idx (P.MintingPolicy script) = do
    let redeemerPtr = P.RedeemerPtr P.Mint (fromIntegral idx)
    P.Redeemer redeemer <- maybe (Left MissingMintingPolicyRedeemer) Right (Map.lookup redeemerPtr redeemers)
    C.PlutusScriptWitness C.PlutusScriptV1InAlonzo C.PlutusScriptV1
        <$> toCardanoPlutusScript script
        <*> pure C.NoScriptDatumForMint
        <*> pure (C.fromPlutusData $ Api.toData redeemer)
        <*> pure zeroExecutionUnits

fromCardanoTxOut :: C.TxOut era -> Either FromCardanoError P.TxOut
fromCardanoTxOut (C.TxOut addr value datumHash) =
    P.TxOut
    <$> fromCardanoAddress addr
    <*> pure (fromCardanoTxOutValue value)
    <*> pure (fromCardanoTxOutDatumHash datumHash)

toCardanoTxOut :: C.NetworkId -> P.TxOut -> Either ToCardanoError (C.TxOut C.AlonzoEra)
toCardanoTxOut networkId (P.TxOut addr value datumHash) =
    C.TxOut <$> toCardanoAddress networkId addr
            <*> toCardanoTxOutValue value
            <*> toCardanoTxOutDatumHash datumHash

fromCardanoAddress :: C.AddressInEra era -> Either FromCardanoError P.Address
fromCardanoAddress (C.AddressInEra C.ByronAddressInAnyEra (C.ByronAddress address)) =
    Right $ P.Address plutusCredential Nothing
    where
      plutusCredential :: Credential.Credential
      plutusCredential =
          Credential.PubKeyCredential
        $ P.PubKeyHash
        $ PlutusTx.toBuiltin
        $ addrToBase58 address

fromCardanoAddress (C.AddressInEra _ (C.ShelleyAddress _ paymentCredential stakeAddressReference)) =
    P.Address (fromCardanoPaymentCredential (C.fromShelleyPaymentCredential paymentCredential))
        <$> fromCardanoStakeAddressReference (C.fromShelleyStakeReference stakeAddressReference)

toCardanoAddress :: C.NetworkId -> P.Address -> Either ToCardanoError (C.AddressInEra C.AlonzoEra)
toCardanoAddress networkId (P.Address addressCredential addressStakingCredential) =
    C.AddressInEra (C.ShelleyAddressInEra C.ShelleyBasedEraAlonzo) <$>
        (C.makeShelleyAddress networkId
            <$> toCardanoPaymentCredential addressCredential
            <*> toCardanoStakeAddressReference addressStakingCredential)

fromCardanoPaymentCredential :: C.PaymentCredential -> Credential.Credential
fromCardanoPaymentCredential (C.PaymentCredentialByKey paymentKeyHash) = Credential.PubKeyCredential (fromCardanoPaymentKeyHash paymentKeyHash)
fromCardanoPaymentCredential (C.PaymentCredentialByScript scriptHash) = Credential.ScriptCredential (fromCardanoScriptHash scriptHash)

toCardanoPaymentCredential :: Credential.Credential -> Either ToCardanoError C.PaymentCredential
toCardanoPaymentCredential (Credential.PubKeyCredential pubKeyHash) = C.PaymentCredentialByKey <$> toCardanoPaymentKeyHash pubKeyHash
toCardanoPaymentCredential (Credential.ScriptCredential validatorHash) = C.PaymentCredentialByScript <$> toCardanoScriptHash validatorHash

fromCardanoPaymentKeyHash :: C.Hash C.PaymentKey -> P.PubKeyHash
fromCardanoPaymentKeyHash paymentKeyHash = P.PubKeyHash $ PlutusTx.toBuiltin $ C.serialiseToRawBytes paymentKeyHash

toCardanoPaymentKeyHash :: P.PubKeyHash -> Either ToCardanoError (C.Hash C.PaymentKey)
toCardanoPaymentKeyHash (P.PubKeyHash bs) =
    let bsx = PlutusTx.fromBuiltin bs
        tg = "toCardanoPaymentKeyHash (" <> show (BS.length bsx) <> " bytes)"
    in tag tg $ deserialiseFromRawBytes (C.AsHash C.AsPaymentKey) bsx

fromCardanoScriptHash :: C.ScriptHash -> P.ValidatorHash
fromCardanoScriptHash scriptHash = P.ValidatorHash $ PlutusTx.toBuiltin $ C.serialiseToRawBytes scriptHash

toCardanoScriptHash :: P.ValidatorHash -> Either ToCardanoError C.ScriptHash
toCardanoScriptHash (P.ValidatorHash bs) = tag "toCardanoScriptHash" $ deserialiseFromRawBytes C.AsScriptHash $ PlutusTx.fromBuiltin bs

fromCardanoStakeAddressReference :: C.StakeAddressReference -> Either FromCardanoError (Maybe Credential.StakingCredential)
fromCardanoStakeAddressReference C.NoStakeAddress = pure Nothing
fromCardanoStakeAddressReference (C.StakeAddressByValue stakeCredential) =
    pure $ Just (Credential.StakingHash $ fromCardanoStakeCredential stakeCredential)
fromCardanoStakeAddressReference C.StakeAddressByPointer{} = pure Nothing

toCardanoStakeAddressReference :: Maybe Credential.StakingCredential -> Either ToCardanoError C.StakeAddressReference
toCardanoStakeAddressReference Nothing = pure C.NoStakeAddress
toCardanoStakeAddressReference (Just (Credential.StakingHash credential)) =
    C.StakeAddressByValue <$> toCardanoStakeCredential credential
toCardanoStakeAddressReference (Just Credential.StakingPtr{}) = Left StakingPointersNotSupported

fromCardanoStakeCredential :: C.StakeCredential -> Credential.Credential
fromCardanoStakeCredential (C.StakeCredentialByKey stakeKeyHash) = Credential.PubKeyCredential (fromCardanoStakeKeyHash stakeKeyHash)
fromCardanoStakeCredential (C.StakeCredentialByScript scriptHash) = Credential.ScriptCredential (fromCardanoScriptHash scriptHash)

toCardanoStakeCredential :: Credential.Credential -> Either ToCardanoError C.StakeCredential
toCardanoStakeCredential (Credential.PubKeyCredential pubKeyHash) = C.StakeCredentialByKey <$> toCardanoStakeKeyHash pubKeyHash
toCardanoStakeCredential (Credential.ScriptCredential validatorHash) = C.StakeCredentialByScript <$> toCardanoScriptHash validatorHash

fromCardanoStakeKeyHash :: C.Hash C.StakeKey -> P.PubKeyHash
fromCardanoStakeKeyHash stakeKeyHash = P.PubKeyHash $ PlutusTx.toBuiltin $ C.serialiseToRawBytes stakeKeyHash

toCardanoStakeKeyHash :: P.PubKeyHash -> Either ToCardanoError (C.Hash C.StakeKey)
toCardanoStakeKeyHash (P.PubKeyHash bs) = tag "toCardanoStakeKeyHash" $ deserialiseFromRawBytes (C.AsHash C.AsStakeKey) (PlutusTx.fromBuiltin bs)

fromCardanoTxOutValue :: C.TxOutValue era -> P.Value
fromCardanoTxOutValue (C.TxOutAdaOnly _ lovelace) = fromCardanoLovelace lovelace
fromCardanoTxOutValue (C.TxOutValue _ value)      = fromCardanoValue value

toCardanoTxOutValue :: P.Value -> Either ToCardanoError (C.TxOutValue C.AlonzoEra)
toCardanoTxOutValue value = do
    when (Ada.fromValue value == mempty) (Left OutputHasZeroAda)
    C.TxOutValue C.MultiAssetInAlonzoEra <$> toCardanoValue value

fromCardanoTxOutDatumHash :: C.TxOutDatumHash era -> Maybe P.DatumHash
fromCardanoTxOutDatumHash C.TxOutDatumHashNone   = Nothing
fromCardanoTxOutDatumHash (C.TxOutDatumHash _ h) = Just $ P.DatumHash $ PlutusTx.toBuiltin (C.serialiseToRawBytes h)

toCardanoTxOutDatumHash :: Maybe P.DatumHash -> Either ToCardanoError (C.TxOutDatumHash C.AlonzoEra)
toCardanoTxOutDatumHash Nothing = pure C.TxOutDatumHashNone
toCardanoTxOutDatumHash (Just (P.DatumHash bs)) = C.TxOutDatumHash C.ScriptDataInAlonzoEra <$> tag "toCardanoTxOutDatumHash" (deserialiseFromRawBytes (C.AsHash C.AsScriptData) (PlutusTx.fromBuiltin bs))

fromCardanoMintValue :: C.TxMintValue build era -> P.Value
fromCardanoMintValue C.TxMintNone              = mempty
fromCardanoMintValue (C.TxMintValue _ value _) = fromCardanoValue value

toCardanoMintValue :: P.Redeemers -> P.Value -> Set.Set P.MintingPolicy -> Either ToCardanoError (C.TxMintValue C.BuildTx C.AlonzoEra)
toCardanoMintValue redeemers value mps =
    C.TxMintValue C.MultiAssetInAlonzoEra
        <$> toCardanoValue value
        <*> (C.BuildTxWith . Map.fromList <$> traverse (\(idx, mp) -> (,) <$> (toCardanoPolicyId . P.mintingPolicyHash) mp <*> toCardanoMintWitness redeemers idx mp) (Prelude.zip [0..] $ Set.toList mps))

fromCardanoValue :: C.Value -> P.Value
fromCardanoValue (C.valueToList -> list) = foldMap toValue list
    where
        toValue (C.AdaAssetId, C.Quantity q) = Ada.lovelaceValueOf q
        toValue (C.AssetId policyId assetName, C.Quantity q)
            = Value.singleton (Value.mpsSymbol $ fromCardanoPolicyId policyId) (fromCardanoAssetName assetName) q

toCardanoValue :: P.Value -> Either ToCardanoError C.Value
toCardanoValue = fmap C.valueFromList . traverse fromValue . Value.flattenValue
    where
        fromValue (currencySymbol, tokenName, amount)
            | currencySymbol == Ada.adaSymbol && tokenName == Ada.adaToken =
                pure (C.AdaAssetId, C.Quantity amount)
            | otherwise =
                (,) <$> (C.AssetId <$> toCardanoPolicyId (Value.currencyMPSHash currencySymbol) <*> pure (toCardanoAssetName tokenName)) <*> pure (C.Quantity amount)

fromCardanoPolicyId :: C.PolicyId -> P.MintingPolicyHash
fromCardanoPolicyId (C.PolicyId scriptHash) = P.MintingPolicyHash $ PlutusTx.toBuiltin (C.serialiseToRawBytes scriptHash)

toCardanoPolicyId :: P.MintingPolicyHash -> Either ToCardanoError C.PolicyId
toCardanoPolicyId (P.MintingPolicyHash bs) = C.PolicyId <$> tag "toCardanoPolicyId" (tag (show (BS.length (PlutusTx.fromBuiltin bs)) <> " bytes") (deserialiseFromRawBytes C.AsScriptHash (PlutusTx.fromBuiltin bs)))

fromCardanoAssetName :: C.AssetName -> Value.TokenName
fromCardanoAssetName (C.AssetName bs) = Value.TokenName $ PlutusTx.toBuiltin bs

toCardanoAssetName :: Value.TokenName -> C.AssetName
toCardanoAssetName (Value.TokenName bs) = C.AssetName $ PlutusTx.fromBuiltin bs

fromCardanoFee :: C.TxFee era -> P.Value
fromCardanoFee (C.TxFeeImplicit _)          = mempty
fromCardanoFee (C.TxFeeExplicit _ lovelace) = fromCardanoLovelace lovelace

toCardanoFee :: P.Value -> Either ToCardanoError (C.TxFee C.AlonzoEra)
toCardanoFee value = C.TxFeeExplicit C.TxFeesExplicitInAlonzoEra <$> toCardanoLovelace value

fromCardanoLovelace :: C.Lovelace -> P.Value
fromCardanoLovelace (C.lovelaceToQuantity -> C.Quantity lovelace) = Ada.lovelaceValueOf lovelace

toCardanoLovelace :: P.Value -> Either ToCardanoError C.Lovelace
toCardanoLovelace value = if value == Ada.lovelaceValueOf lovelace then pure . C.quantityToLovelace . C.Quantity $ lovelace else Left ValueNotPureAda
    where
        Ada.Lovelace lovelace = Ada.fromValue value

fromCardanoValidityRange :: (C.TxValidityLowerBound era, C.TxValidityUpperBound era) -> P.SlotRange
fromCardanoValidityRange (l, u) = P.Interval (fromCardanoValidityLowerBound l) (fromCardanoValidityUpperBound u)

toCardanoValidityRange :: P.SlotRange -> Either ToCardanoError (C.TxValidityLowerBound C.AlonzoEra, C.TxValidityUpperBound C.AlonzoEra)
toCardanoValidityRange (P.Interval l u) = (,) <$> toCardanoValidityLowerBound l <*> toCardanoValidityUpperBound u

fromCardanoValidityLowerBound :: C.TxValidityLowerBound era -> P.LowerBound P.Slot
fromCardanoValidityLowerBound C.TxValidityNoLowerBound = P.LowerBound P.NegInf True
fromCardanoValidityLowerBound (C.TxValidityLowerBound _ slotNo) = P.LowerBound (P.Finite $ fromCardanoSlotNo slotNo) True

toCardanoValidityLowerBound :: P.LowerBound P.Slot -> Either ToCardanoError (C.TxValidityLowerBound C.AlonzoEra)
toCardanoValidityLowerBound (P.LowerBound P.NegInf _) = pure C.TxValidityNoLowerBound
toCardanoValidityLowerBound (P.LowerBound (P.Finite slotNo) closed)
    = pure . C.TxValidityLowerBound C.ValidityLowerBoundInAlonzoEra . toCardanoSlotNo $ if closed then slotNo else slotNo + 1
toCardanoValidityLowerBound (P.LowerBound P.PosInf _) = Left InvalidValidityRange

fromCardanoValidityUpperBound :: C.TxValidityUpperBound era -> P.UpperBound P.Slot
fromCardanoValidityUpperBound (C.TxValidityNoUpperBound _) = P.UpperBound P.PosInf True
fromCardanoValidityUpperBound (C.TxValidityUpperBound _ slotNo) = P.UpperBound (P.Finite $ fromCardanoSlotNo slotNo) False

toCardanoValidityUpperBound :: P.UpperBound P.Slot -> Either ToCardanoError (C.TxValidityUpperBound C.AlonzoEra)
toCardanoValidityUpperBound (P.UpperBound P.PosInf _) = pure $ C.TxValidityNoUpperBound C.ValidityNoUpperBoundInAlonzoEra
toCardanoValidityUpperBound (P.UpperBound (P.Finite slotNo) closed)
    = pure . C.TxValidityUpperBound C.ValidityUpperBoundInAlonzoEra . toCardanoSlotNo $ if closed then slotNo + 1 else slotNo
toCardanoValidityUpperBound (P.UpperBound P.NegInf _) = Left InvalidValidityRange

fromCardanoSlotNo :: C.SlotNo -> P.Slot
fromCardanoSlotNo (C.SlotNo w64) = P.Slot (toInteger w64)

toCardanoSlotNo :: P.Slot -> C.SlotNo
toCardanoSlotNo (P.Slot i) = C.SlotNo (fromInteger i)

fromCardanoExtraScriptData :: C.TxExtraScriptData era -> [P.Datum]
fromCardanoExtraScriptData C.TxExtraScriptDataNone            = []
fromCardanoExtraScriptData (C.TxExtraScriptData _ scriptData) = fmap (P.Datum . fromCardanoScriptData) scriptData

toCardanoExtraScriptData :: [P.Datum] -> C.TxExtraScriptData C.AlonzoEra
toCardanoExtraScriptData = C.TxExtraScriptData C.ScriptDataInAlonzoEra . fmap (toCardanoScriptData . P.getDatum)

fromCardanoScriptData :: C.ScriptData -> Api.BuiltinData
fromCardanoScriptData = Api.dataToBuiltinData . C.toPlutusData

toCardanoScriptData :: Api.BuiltinData -> C.ScriptData
toCardanoScriptData = C.fromPlutusData . Api.builtinDataToData

fromCardanoScriptInEra :: C.ScriptInEra era -> Maybe P.Script
fromCardanoScriptInEra (C.ScriptInEra C.PlutusScriptV1InAlonzo (C.PlutusScript C.PlutusScriptV1 script)) =
    Just $ fromCardanoPlutusScript script
fromCardanoScriptInEra (C.ScriptInEra _ C.SimpleScript{}) = Nothing

toCardanoScriptInEra :: P.Script -> Either ToCardanoError (C.ScriptInEra C.AlonzoEra)
toCardanoScriptInEra script = C.ScriptInEra C.PlutusScriptV1InAlonzo . C.PlutusScript C.PlutusScriptV1 <$> toCardanoPlutusScript script

fromCardanoPlutusScript :: C.HasTypeProxy lang => C.PlutusScript lang -> P.Script
fromCardanoPlutusScript = Codec.deserialise . BSL.fromStrict . C.serialiseToRawBytes

toCardanoPlutusScript :: P.Script -> Either ToCardanoError (C.PlutusScript C.PlutusScriptV1)
toCardanoPlutusScript =
    tag "toCardanoPlutusScript"
    . deserialiseFromRawBytes (C.AsPlutusScript C.AsPlutusScriptV1) . BSL.toStrict . Codec.serialise

deserialiseFromRawBytes :: C.SerialiseAsRawBytes t => C.AsType t -> ByteString -> Either ToCardanoError t
deserialiseFromRawBytes asType = maybe (Left DeserialisationError) Right . C.deserialiseFromRawBytes asType

tag :: String -> Either ToCardanoError t -> Either ToCardanoError t
tag s = first (Tag s)

data FromCardanoError
    = SimpleScriptsNotSupported
    deriving stock (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON, ToObject)

instance Pretty FromCardanoError where
    pretty SimpleScriptsNotSupported        = "Simple scripts are not supported"
    -- pretty StakeAddressPointersNotSupported = "Stake address pointers are not supported"

data ToCardanoError
    = EvaluationError Api.EvaluationError
    | TxBodyError C.TxBodyError
    | DeserialisationError
    | InvalidValidityRange
    | ValueNotPureAda
    | OutputHasZeroAda
    | StakingPointersNotSupported
    | SimpleScriptsNotSupportedToCardano
    | MissingTxInType
    | MissingMintingPolicyRedeemer
    | Tag String ToCardanoError

instance Pretty ToCardanoError where
    pretty (EvaluationError err)              = "EvaluationError" <> colon <+> pretty err
    pretty (TxBodyError err)                  = "TxBodyError" <> colon <+> pretty (C.displayError err)
    pretty DeserialisationError               = "ByteString deserialisation failed"
    pretty InvalidValidityRange               = "Invalid validity range"
    pretty ValueNotPureAda                    = "Fee values should only contain Ada"
    pretty OutputHasZeroAda                   = "Transaction outputs should not contain zero Ada"
    pretty StakingPointersNotSupported        = "Staking pointers are not supported"
    pretty SimpleScriptsNotSupportedToCardano = "Simple scripts are not supported"
    pretty MissingTxInType                    = "Missing TxInType"
    pretty MissingMintingPolicyRedeemer       = "Missing minting policy redeemer"
    pretty (Tag t err)                        = pretty t <> colon <+> pretty err

zeroExecutionUnits :: C.ExecutionUnits
zeroExecutionUnits = C.ExecutionUnits 0 0
