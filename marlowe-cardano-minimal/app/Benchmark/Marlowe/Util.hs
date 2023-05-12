
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RecordWildCards     #-}


module Benchmark.Marlowe.Util (
  lovelace
, makeInput
, makeOutput
, makeRedeemerMap
, makeDatumMap
, makeBuiltinData
, updateScriptHash
) where


import Codec.Serialise (deserialise)
import PlutusLedgerApi.V2 (Address (Address), BuiltinData, Credential (..), Datum (Datum),
                           DatumHash, LedgerBytes (getLedgerBytes),
                           OutputDatum (NoOutputDatum, OutputDatumHash), Redeemer (Redeemer),
                           ScriptContext (..), ScriptHash, ScriptPurpose, TxId, TxInInfo (..),
                           TxInfo (..), TxOut (..), TxOutRef (TxOutRef), Value, adaSymbol, adaToken,
                           dataToBuiltinData, fromBuiltin, singleton)

import Data.ByteString.Lazy qualified as LBS (fromStrict)
import PlutusTx.AssocMap qualified as AM (Map, singleton)


lovelace
  :: Integer
  -> Value
lovelace = singleton adaSymbol adaToken


makeInput
  :: TxId
  -> Integer
  -> Credential
  -> Value
  -> Maybe DatumHash
  -> Maybe ScriptHash
  -> TxInInfo
makeInput txId txIx credential value datum script =
  TxInInfo
    (TxOutRef txId txIx)
    (makeOutput credential value datum script)


makeOutput
  :: Credential
  -> Value
  -> Maybe DatumHash
  -> Maybe ScriptHash
  -> TxOut
makeOutput credential value =
  TxOut (Address credential Nothing) value
    . maybe NoOutputDatum OutputDatumHash


makeRedeemerMap
  :: ScriptPurpose
  -> LedgerBytes
  -> AM.Map ScriptPurpose Redeemer
makeRedeemerMap = (. (Redeemer . makeBuiltinData)) . AM.singleton


makeDatumMap
  :: DatumHash
  -> LedgerBytes
  -> AM.Map DatumHash Datum
makeDatumMap = (. (Datum . makeBuiltinData)) . AM.singleton


makeBuiltinData
  :: LedgerBytes
  -> BuiltinData
makeBuiltinData =
  dataToBuiltinData
    . deserialise
    . LBS.fromStrict
    . fromBuiltin
    . getLedgerBytes


updateScriptHash
  :: ScriptHash
  -> ScriptHash
  -> ScriptContext
  -> ScriptContext
updateScriptHash oldHash newHash scriptContext =
  let
    updateAddress address@(Address (ScriptCredential hash) stakeCredential)
      | hash == oldHash = Address (ScriptCredential newHash) stakeCredential
      | otherwise = address
    updateAddress address = address
    updateTxOut txOut@TxOut{..} = txOut {txOutAddress = updateAddress txOutAddress}
    updateTxInInfo txInInfo@TxInInfo{..} =
      txInInfo {txInInfoResolved = updateTxOut txInInfoResolved}
    txInfo@TxInfo{..} = scriptContextTxInfo scriptContext
    txInfo' =
      txInfo
      {
        txInfoInputs = updateTxInInfo <$> txInfoInputs
      , txInfoOutputs = updateTxOut <$> txInfoOutputs
      }
  in
    scriptContext
    {
      scriptContextTxInfo = txInfo'
    }
