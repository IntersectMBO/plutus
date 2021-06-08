{-# LANGUAGE GADTs           #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns    #-}
{-|

Interface to the transaction types from 'cardano-api'

-}
module Plutus.Contract.CardanoAPI(
    fromCardanoTx
  , fromCardanoTxIn
  , fromCardanoTxInsCollateral
  , fromCardanoTxInWitness
  , fromCardanoTxOut
  , fromCardanoMintValue
  , fromCardanoValue
  , fromCardanoFee
  , fromCardanoValidityRange
  , fromCardanoAuxScriptData
  , fromCardanoTxAuxScripts
  , toCardanoTxIn
  , toCardanoTxInsCollateral
  , toCardanoTxInWitness
  , toCardanoTxOut
  , toCardanoMintValue
  , toCardanoValue
  , toCardanoFee
  , toCardanoValidityRange
  , toCardanoAuxScriptData
  , toCardanoTxAuxScripts
) where

import qualified Cardano.Api            as C
import qualified Cardano.Api.Shelley    as C
import qualified Cardano.Ledger.Era     as C
import qualified Codec.Serialise        as Codec
import qualified Data.ByteString.Lazy   as BSL
import           Data.ByteString.Short  as BSS
import qualified Data.Map               as Map
import           Data.Maybe             (mapMaybe)
import qualified Data.Set               as Set
import qualified Ledger                 as P
import qualified Ledger.Ada             as Ada
import qualified Plutus.V1.Ledger.Api   as Api
import qualified Plutus.V1.Ledger.Value as Value
import qualified PlutusTx.Data          as Data

fromCardanoTx :: C.Era era => C.Tx era -> P.Tx
fromCardanoTx (C.Tx (C.TxBody C.TxBodyContent{..}) keyWitnesses) = P.Tx
  { txInputs = Set.fromList $ fmap (P.pubKeyTxIn . fromCardanoTxIn . fst) txIns -- TODO: can create TxInType only with a Build Tx
  , txCollateral = fromCardanoTxInsCollateral txInsCollateral
  , txOutputs = map fromCardanoTxOut txOuts
  , txForge = fromCardanoMintValue txMintValue
  , txFee = fromCardanoFee txFee
  , txValidRange = fromCardanoValidityRange txValidityRange
  , txData = Map.fromList $ fmap (\ds -> (P.datumHash ds, ds)) $ fromCardanoAuxScriptData txAuxScriptData
  , txSignatures = fromCardanoKeyWitnesses keyWitnesses -- TODO: also use txExtraKeyWits?
  , txForgeScripts = fromCardanoTxAuxScripts txAuxScripts -- TODO: is this correct?
  -- not used from Cardano Tx: txMetadata, txExtraKeyWits, txProtocolParams, txWithdrawals, txCertificates, txUpdateProposal
  }

fromCardanoTxIn :: C.TxIn -> P.TxOutRef
fromCardanoTxIn (C.TxIn txId (C.TxIx txIx)) = P.TxOutRef (fromCardanoTxId txId) (toInteger txIx)

toCardanoTxIn :: P.TxOutRef -> Maybe C.TxIn
toCardanoTxIn (P.TxOutRef txId txIx) = C.TxIn <$> toCardanoTxId txId <*> pure (C.TxIx (fromInteger txIx))

fromCardanoTxId :: C.TxId -> P.TxId
fromCardanoTxId txId = P.TxId $ C.serialiseToRawBytes txId

toCardanoTxId :: P.TxId -> Maybe C.TxId
toCardanoTxId (P.TxId bs) = C.deserialiseFromRawBytes C.AsTxId bs

fromCardanoTxInsCollateral :: C.TxInsCollateral era -> Set.Set P.TxIn
fromCardanoTxInsCollateral C.TxInsCollateralNone       = mempty
fromCardanoTxInsCollateral (C.TxInsCollateral _ txIns) = Set.fromList $ fmap (P.pubKeyTxIn . fromCardanoTxIn) txIns

toCardanoTxInsCollateral :: Set.Set P.TxIn -> Maybe (C.TxInsCollateral C.AlonzoEra)
toCardanoTxInsCollateral = fmap (C.TxInsCollateral C.CollateralInAlonzoEra) . traverse (toCardanoTxIn . P.txInRef) . Set.toList

fromCardanoTxInWitness :: C.Witness C.WitCtxTxIn era -> Maybe P.TxInType
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
fromCardanoTxInWitness _ = Nothing

toCardanoTxInWitness :: P.TxInType -> Maybe (C.Witness C.WitCtxTxIn C.AlonzoEra)
toCardanoTxInWitness P.ConsumePublicKeyAddress = pure (C.KeyWitness C.KeyWitnessForSpending)
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
        <*> toCardanoExecutionUnits validator [datum] -- TODO: is [datum] correct?
        )

fromCardanoTxOut :: C.TxOut era -> P.TxOut
fromCardanoTxOut (C.TxOut addr value datumHash) = P.TxOut (fromCardanoAddress addr) (fromCardanoTxOutValue value) (fromCardanoTxOutDatumHash datumHash)

toCardanoTxOut :: P.TxOut -> Maybe (C.TxOut C.AlonzoEra)
toCardanoTxOut (P.TxOut addr value datumHash) = C.TxOut <$> toCardanoAddress addr <*> toCardanoTxOutValue value <*> toCardanoTxOutDatumHash datumHash

fromCardanoAddress :: C.AddressInEra era -> P.Address
fromCardanoAddress = fromCardanoAddress -- TODO

toCardanoAddress :: P.Address -> Maybe (C.AddressInEra C.AlonzoEra)
toCardanoAddress = toCardanoAddress -- TODO

fromCardanoTxOutValue :: C.TxOutValue era -> P.Value
fromCardanoTxOutValue (C.TxOutAdaOnly _ lovelace) = fromCardanoLovelace lovelace
fromCardanoTxOutValue (C.TxOutValue _ value)      = fromCardanoValue value

toCardanoTxOutValue :: P.Value -> Maybe (C.TxOutValue C.AlonzoEra)
toCardanoTxOutValue value = C.TxOutValue C.MultiAssetInAlonzoEra <$> toCardanoValue value

fromCardanoTxOutDatumHash :: C.TxOutDatumHash era -> Maybe P.DatumHash
fromCardanoTxOutDatumHash C.TxOutDatumHashNone   = Nothing
fromCardanoTxOutDatumHash (C.TxOutDatumHash _ h) = Just $ P.DatumHash (C.serialiseToRawBytes h)

toCardanoTxOutDatumHash :: Maybe P.DatumHash -> Maybe (C.TxOutDatumHash C.AlonzoEra)
toCardanoTxOutDatumHash Nothing = pure C.TxOutDatumHashNone
toCardanoTxOutDatumHash (Just (P.DatumHash bs)) = C.TxOutDatumHash C.ScriptDataInAlonzoEra <$> C.deserialiseFromRawBytes (C.AsHash C.AsScriptData) bs

fromCardanoMintValue :: C.TxMintValue build era -> P.Value
fromCardanoMintValue C.TxMintNone              = mempty
fromCardanoMintValue (C.TxMintValue _ value _) = fromCardanoValue value

toCardanoMintValue :: P.Value -> Maybe (C.TxMintValue C.ViewTx C.AlonzoEra)
toCardanoMintValue value = C.TxMintValue C.MultiAssetInAlonzoEra <$> toCardanoValue value <*> pure C.ViewTx

fromCardanoValue :: C.Value -> P.Value
fromCardanoValue (C.valueToList -> list) = foldMap toValue list
    where
        toValue (C.AdaAssetId, C.Quantity q) = Ada.lovelaceValueOf q
        toValue (C.AssetId policyId assetName, C.Quantity q)
            = Value.singleton (fromCardanoPolicyId policyId) (fromCardanoAssetName assetName) q

toCardanoValue :: P.Value -> Maybe C.Value
toCardanoValue = fmap C.valueFromList . traverse fromValue . Value.flattenValue
    where
        fromValue (currencySymbol, tokenName, amount) =
            (,) <$> (C.AssetId <$> toCardanoPolicyId currencySymbol <*> pure (toCardanoAssetName tokenName)) <*> pure (C.Quantity amount)

fromCardanoPolicyId :: C.PolicyId -> Value.CurrencySymbol
fromCardanoPolicyId (C.PolicyId scriptHash) = Value.CurrencySymbol (C.serialiseToRawBytes scriptHash)

toCardanoPolicyId :: Value.CurrencySymbol -> Maybe C.PolicyId
toCardanoPolicyId (Value.CurrencySymbol bs) = C.PolicyId <$> C.deserialiseFromRawBytes C.AsScriptHash bs

fromCardanoAssetName :: C.AssetName -> Value.TokenName
fromCardanoAssetName (C.AssetName bs) = Value.TokenName bs

toCardanoAssetName :: Value.TokenName -> C.AssetName
toCardanoAssetName (Value.TokenName bs) = C.AssetName bs

fromCardanoFee :: C.TxFee era -> P.Value
fromCardanoFee (C.TxFeeImplicit _)          = mempty
fromCardanoFee (C.TxFeeExplicit _ lovelace) = fromCardanoLovelace lovelace

toCardanoFee :: P.Value -> Maybe (C.TxFee C.AlonzoEra)
toCardanoFee value = C.TxFeeExplicit C.TxFeesExplicitInAlonzoEra <$> toCardanoLovelace value

fromCardanoLovelace :: C.Lovelace -> P.Value
fromCardanoLovelace (C.lovelaceToQuantity -> C.Quantity lovelace) = Ada.lovelaceValueOf lovelace

toCardanoLovelace :: P.Value -> Maybe C.Lovelace
toCardanoLovelace value = if value == Ada.lovelaceValueOf lovelace then pure . C.quantityToLovelace . C.Quantity $ lovelace else Nothing
    where
        Ada.Lovelace lovelace = Ada.fromValue value

fromCardanoValidityRange :: (C.TxValidityLowerBound era, C.TxValidityUpperBound era) -> P.SlotRange
fromCardanoValidityRange (l, u) = P.Interval (fromCardanoValidityLowerBound l) (fromCardanoValidityUpperBound u)

toCardanoValidityRange :: P.SlotRange -> Maybe (C.TxValidityLowerBound C.AlonzoEra, C.TxValidityUpperBound C.AlonzoEra)
toCardanoValidityRange (P.Interval l u) = (,) <$> toCardanoValidityLowerBound l <*> toCardanoValidityUpperBound u

fromCardanoValidityLowerBound :: C.TxValidityLowerBound era -> P.LowerBound P.Slot
fromCardanoValidityLowerBound C.TxValidityNoLowerBound = P.LowerBound P.NegInf True
fromCardanoValidityLowerBound (C.TxValidityLowerBound _ slotNo) = P.LowerBound (P.Finite $ fromCardanoSlotNo slotNo) True -- TODO: inclusive or exclusive?

toCardanoValidityLowerBound :: P.LowerBound P.Slot -> Maybe (C.TxValidityLowerBound C.AlonzoEra)
toCardanoValidityLowerBound (P.LowerBound P.NegInf _) = pure C.TxValidityNoLowerBound
toCardanoValidityLowerBound (P.LowerBound (P.Finite slotNo) _) = pure $ C.TxValidityLowerBound C.ValidityLowerBoundInAlonzoEra $ toCardanoSlotNo slotNo -- TODO: inclusive or exclusive?
toCardanoValidityLowerBound (P.LowerBound P.PosInf _) = Nothing

fromCardanoValidityUpperBound :: C.TxValidityUpperBound era -> P.UpperBound P.Slot
fromCardanoValidityUpperBound (C.TxValidityNoUpperBound _) = P.UpperBound P.PosInf True
fromCardanoValidityUpperBound (C.TxValidityUpperBound _ slotNo) = P.UpperBound (P.Finite $ fromCardanoSlotNo slotNo) True -- TODO: inclusive or exclusive?

toCardanoValidityUpperBound :: P.UpperBound P.Slot -> Maybe (C.TxValidityUpperBound C.AlonzoEra)
toCardanoValidityUpperBound (P.UpperBound P.PosInf _) = pure $ C.TxValidityNoUpperBound C.ValidityNoUpperBoundInAlonzoEra
toCardanoValidityUpperBound (P.UpperBound (P.Finite slotNo) _) = pure $ C.TxValidityUpperBound C.ValidityUpperBoundInAlonzoEra $ toCardanoSlotNo slotNo -- TODO: inclusive or exclusive?
toCardanoValidityUpperBound (P.UpperBound P.NegInf _) = Nothing

fromCardanoSlotNo :: C.SlotNo -> P.Slot
fromCardanoSlotNo (C.SlotNo w64) = P.Slot (toInteger w64)

toCardanoSlotNo :: P.Slot -> C.SlotNo
toCardanoSlotNo (P.Slot i) = C.SlotNo (fromInteger i)

fromCardanoAuxScriptData :: C.TxAuxScriptData era -> [P.Datum]
fromCardanoAuxScriptData C.TxAuxScriptDataNone            = []
fromCardanoAuxScriptData (C.TxAuxScriptData _ scriptData) = fmap (P.Datum . fromCardanoScriptData) scriptData

toCardanoAuxScriptData :: [P.Datum] -> C.TxAuxScriptData C.AlonzoEra
toCardanoAuxScriptData = C.TxAuxScriptData C.ScriptDataInAlonzoEra . fmap (toCardanoScriptData . P.getDatum)

fromCardanoScriptData :: C.ScriptData -> Data.Data
fromCardanoScriptData = C.toPlutusData

toCardanoScriptData :: Data.Data -> C.ScriptData
toCardanoScriptData = C.fromPlutusData

fromCardanoKeyWitnesses :: [C.KeyWitness era] -> Map.Map P.PubKey P.Signature
fromCardanoKeyWitnesses = fromCardanoKeyWitnesses -- TODO

fromCardanoTxAuxScripts :: C.TxAuxScripts era -> Set.Set P.MonetaryPolicy
fromCardanoTxAuxScripts C.TxAuxScriptsNone = mempty
fromCardanoTxAuxScripts (C.TxAuxScripts _ scripts) = Set.fromList . mapMaybe (fmap P.MonetaryPolicy . fromCardanoScriptInEra) $ scripts

toCardanoTxAuxScripts :: Set.Set P.MonetaryPolicy -> Maybe (C.TxAuxScripts C.AlonzoEra)
toCardanoTxAuxScripts = fmap (C.TxAuxScripts C.AuxScriptsInAlonzoEra) . traverse (toCardanoScriptInEra . P.getMonetaryPolicy) . Set.toList

fromCardanoScriptInEra :: C.ScriptInEra era -> Maybe P.Script
fromCardanoScriptInEra (C.ScriptInEra C.PlutusScriptV1InAlonzo (C.PlutusScript C.PlutusScriptV1 script)) =
    pure $ fromCardanoPlutusScript script
fromCardanoScriptInEra _ = Nothing

toCardanoScriptInEra :: P.Script -> Maybe (C.ScriptInEra C.AlonzoEra)
toCardanoScriptInEra script = C.ScriptInEra C.PlutusScriptV1InAlonzo . C.PlutusScript C.PlutusScriptV1 <$> toCardanoPlutusScript script

fromCardanoPlutusScript :: C.HasTypeProxy lang => C.PlutusScript lang -> P.Script
fromCardanoPlutusScript = Codec.deserialise . BSL.fromStrict . C.serialiseToRawBytes

toCardanoPlutusScript :: P.Script -> Maybe (C.PlutusScript C.PlutusScriptV1)
toCardanoPlutusScript = C.deserialiseFromRawBytes (C.AsPlutusScript C.AsPlutusScriptV1) . BSL.toStrict . Codec.serialise

toCardanoExecutionUnits :: P.Script -> [Data.Data] -> Maybe C.ExecutionUnits
toCardanoExecutionUnits script datum = do
    cmp <- Api.defaultCostModelParams
    let apiScript = BSS.toShort . BSL.toStrict $ Codec.serialise script
    case Api.evaluateScriptCounting Api.Quiet cmp apiScript datum of
        (_, Left _) -> Nothing
        (_, Right (Api.ExBudget (Api.ExCPU cpu) (Api.ExMemory memory))) ->
            pure $ C.ExecutionUnits (fromInteger $ toInteger cpu) (fromInteger $ toInteger memory)
