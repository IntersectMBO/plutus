
-----------------------------------------------------------------------------
--
-- Module      :  $Headers
-- License     :  Apache 2.0
--
-- Stability   :  Experimental
-- Portability :  Portable
--
-- | Utility functions for creating script contexts.
--
-----------------------------------------------------------------------------


{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RecordWildCards     #-}


module Benchmark.Marlowe.Util (
  -- * Conversion
  lovelace
, makeInput
, makeOutput
, makeRedeemerMap
, makeDatumMap
, makeBuiltinData
  -- * Rewriting
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


-- | Integer to lovelace.
lovelace
  :: Integer
  -> Value
lovelace = singleton adaSymbol adaToken


-- Construct a `TxInInfo`.
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


-- Construct a `TxOut`.
makeOutput
  :: Credential
  -> Value
  -> Maybe DatumHash
  -> Maybe ScriptHash
  -> TxOut
makeOutput credential value =
  TxOut (Address credential Nothing) value
    . maybe NoOutputDatum OutputDatumHash


-- Construct a map of redemers.
makeRedeemerMap
  :: ScriptPurpose
  -> LedgerBytes
  -> AM.Map ScriptPurpose Redeemer
makeRedeemerMap = (. (Redeemer . makeBuiltinData)) . AM.singleton


-- Construct a map of datum hashes to datums.
makeDatumMap
  :: DatumHash
  -> LedgerBytes
  -> AM.Map DatumHash Datum
makeDatumMap = (. (Datum . makeBuiltinData)) . AM.singleton


-- Convert ledger bytes to builtin data.
makeBuiltinData
  :: LedgerBytes
  -> BuiltinData
makeBuiltinData =
  dataToBuiltinData
    . deserialise
    . LBS.fromStrict
    . fromBuiltin
    . getLedgerBytes


-- Rewrite all of a particular script hash in the script context.
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
