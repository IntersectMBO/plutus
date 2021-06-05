{-# LANGUAGE GADTs           #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns    #-}
{-

Interface to the transaction types from 'cardano-api'

-}
module Plutus.Contract.CardanoAPI(
    fromCardanoTx
  , fromCardanoTxInWitness
  , fromCardanoValue
) where

import qualified Cardano.Api            as C
import qualified Cardano.Ledger.Era     as C
import           Codec.Serialise        (deserialise)
import           Data.Bifunctor         (bimap)
import qualified Data.ByteString.Lazy   as BSL
import qualified Data.Map               as Map
import           Data.Maybe             (mapMaybe)
import qualified Data.Set               as Set
import qualified Ledger                 as P
import qualified Ledger.Ada             as Ada
import qualified Plutus.V1.Ledger.Value as Value
import qualified PlutusTx.Data          as Data

fromCardanoTx :: C.Era era => C.Tx era -> P.Tx
fromCardanoTx (C.Tx (C.TxBody (C.TxBodyContent{..})) keyWitnesses) = P.Tx
  { txInputs = Set.fromList $ fmap (P.pubKeyTxIn . fromCardanoTxIn . fst) $ txIns -- TODO: can create TxInType only with a Build Tx
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

fromCardanoTxId :: C.TxId -> P.TxId
fromCardanoTxId txId = P.TxId $ C.serialiseToRawBytes txId

fromCardanoTxInsCollateral :: C.TxInsCollateral era -> Set.Set P.TxIn
fromCardanoTxInsCollateral C.TxInsCollateralNone       = mempty
fromCardanoTxInsCollateral (C.TxInsCollateral _ txIns) = Set.fromList $ map (P.pubKeyTxIn . fromCardanoTxIn) $ txIns

fromCardanoTxInWitness :: C.Witness C.WitCtxTxIn era -> Maybe P.TxInType
fromCardanoTxInWitness (C.KeyWitness C.KeyWitnessForSpending) = Just P.ConsumePublicKeyAddress
fromCardanoTxInWitness
    (C.ScriptWitness _
        (C.PlutusScriptWitness
            C.PlutusScriptV1InAlonzo
            C.PlutusScriptV1
            script
            (C.ScriptDatumForTxIn datum)
            redeemer
            _))
    = Just $ P.ConsumeScriptAddress
        (P.Validator $ fromCardanoPlutusScript script)
        (P.Redeemer $ fromCardanoScriptData redeemer)
        (P.Datum $ fromCardanoScriptData datum)
fromCardanoTxInWitness _ = Nothing

fromCardanoTxOut :: C.TxOut era -> P.TxOut
fromCardanoTxOut (C.TxOut addr value datumHash) = P.TxOut (fromCardanoAddress addr) (fromCardanoTxOutValue value) (fromCardanoTxOutDatumHash datumHash)

fromCardanoAddress :: C.AddressInEra era -> P.Address
fromCardanoAddress = fromCardanoAddress -- TODO

fromCardanoTxOutValue :: C.TxOutValue era -> P.Value
fromCardanoTxOutValue (C.TxOutAdaOnly _ lovelace) = fromCardanoLovelace lovelace
fromCardanoTxOutValue (C.TxOutValue _ value)      = fromCardanoValue value

fromCardanoTxOutDatumHash :: C.TxOutDatumHash era -> Maybe P.DatumHash
fromCardanoTxOutDatumHash C.TxOutDatumHashNone   = Nothing
fromCardanoTxOutDatumHash (C.TxOutDatumHash _ h) = Just $ P.DatumHash (C.serialiseToRawBytes h)

fromCardanoMintValue :: C.TxMintValue build era -> P.Value
fromCardanoMintValue C.TxMintNone              = mempty
fromCardanoMintValue (C.TxMintValue _ value _) = fromCardanoValue value

fromCardanoValue :: C.Value -> P.Value
fromCardanoValue (C.valueToList -> list) = foldMap toValue list
  where
    toValue (C.AdaAssetId, C.Quantity q) = Ada.lovelaceValueOf q
    toValue (C.AssetId policyId assetName, C.Quantity q)
      = Value.singleton (fromCardanoPolicyId policyId) (fromCardanoAssetName assetName) q

fromCardanoPolicyId :: C.PolicyId -> Value.CurrencySymbol
fromCardanoPolicyId (C.PolicyId scriptHash) = Value.CurrencySymbol (C.serialiseToRawBytes scriptHash)

fromCardanoAssetName :: C.AssetName -> Value.TokenName
fromCardanoAssetName (C.AssetName bs) = Value.TokenName bs

fromCardanoFee :: C.TxFee era -> P.Value
fromCardanoFee (C.TxFeeImplicit _)          = mempty
fromCardanoFee (C.TxFeeExplicit _ lovelace) = fromCardanoLovelace lovelace

fromCardanoLovelace :: C.Lovelace -> P.Value
fromCardanoLovelace (C.lovelaceToQuantity -> C.Quantity lovelace) = Ada.lovelaceValueOf lovelace

fromCardanoValidityRange :: (C.TxValidityLowerBound era, C.TxValidityUpperBound era) -> P.SlotRange
fromCardanoValidityRange (l, u) = P.Interval (fromCardanoValidityLowerBound l) (fromCardanoValidityUpperBound u)

fromCardanoValidityLowerBound :: C.TxValidityLowerBound era -> P.LowerBound P.Slot
fromCardanoValidityLowerBound C.TxValidityNoLowerBound = P.LowerBound P.NegInf True
fromCardanoValidityLowerBound (C.TxValidityLowerBound _ slotNo) = P.LowerBound (P.Finite $ fromCardanoSlotNo slotNo) True -- TODO: inclusive or exclusive?

fromCardanoValidityUpperBound :: C.TxValidityUpperBound era -> P.UpperBound P.Slot
fromCardanoValidityUpperBound (C.TxValidityNoUpperBound _) = P.UpperBound P.PosInf True
fromCardanoValidityUpperBound (C.TxValidityUpperBound _ slotNo) = P.UpperBound (P.Finite $ fromCardanoSlotNo slotNo) True -- TODO: inclusive or exclusive?

fromCardanoSlotNo :: C.SlotNo -> P.Slot
fromCardanoSlotNo (C.SlotNo w64) = P.Slot (toInteger w64)

fromCardanoAuxScriptData :: C.TxAuxScriptData era -> [P.Datum]
fromCardanoAuxScriptData C.TxAuxScriptDataNone            = []
fromCardanoAuxScriptData (C.TxAuxScriptData _ scriptData) = fmap (P.Datum . fromCardanoScriptData) scriptData

-- TODO: replace with C.toPlutusData, but it is not exported
fromCardanoScriptData :: C.ScriptData -> Data.Data
fromCardanoScriptData (C.ScriptDataConstructor i args) = Data.Constr i $ fmap fromCardanoScriptData args
fromCardanoScriptData (C.ScriptDataMap kvs) = Data.Map $ fmap (bimap fromCardanoScriptData fromCardanoScriptData) kvs
fromCardanoScriptData (C.ScriptDataList xs) = Data.List $ fmap fromCardanoScriptData xs
fromCardanoScriptData (C.ScriptDataNumber i) = Data.I i
fromCardanoScriptData (C.ScriptDataBytes bs) = Data.B bs

fromCardanoKeyWitnesses :: [C.KeyWitness era] -> Map.Map P.PubKey P.Signature
fromCardanoKeyWitnesses = fromCardanoKeyWitnesses -- TODO

fromCardanoTxAuxScripts :: C.TxAuxScripts era -> Set.Set P.MonetaryPolicy
fromCardanoTxAuxScripts C.TxAuxScriptsNone = mempty
fromCardanoTxAuxScripts (C.TxAuxScripts _ scripts) = Set.fromList . mapMaybe (fmap P.MonetaryPolicy . fromCardanoScriptInEra) $ scripts

fromCardanoScriptInEra :: C.ScriptInEra era -> Maybe P.Script
fromCardanoScriptInEra (C.ScriptInEra C.PlutusScriptV1InAlonzo (C.PlutusScript C.PlutusScriptV1 script)) =
  Just $ fromCardanoPlutusScript script
fromCardanoScriptInEra _ = Nothing -- TODO: throw error, or maybe SimpleScripts actually are supported?

fromCardanoPlutusScript :: C.PlutusScript lang -> P.Script
fromCardanoPlutusScript = deserialise . BSL.fromStrict . C.serialiseToRawBytes

-- TODO: Conversion functions between our Tx types and those from Cardano.Api
-- https://input-output-hk.github.io/cardano-node/cardano-api/Cardano-Api.html
