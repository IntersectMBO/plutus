
-- editorconfig-checker-disable-file


-----------------------------------------------------------------------------
--
-- Module      :  $Headers
-- License     :  Apache 2.0
--
-- Stability   :  Experimental
-- Portability :  Portable
--
-- | Benchmarking support for Marlowe's semantics validator.
--
-----------------------------------------------------------------------------


{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}


module Benchmark.Marlowe.Semantics (
  -- * Benchmarking
  benchmarks
, validatorBytes
, validatorHash
, exampleBenchmark
) where


import Benchmark.Marlowe (readBenchmarks)
import Benchmark.Marlowe.Types (Benchmark (..), makeBenchmark)
import Benchmark.Marlowe.Util (lovelace, makeBuiltinData, makeDatumMap, makeInput, makeOutput,
                               makeRedeemerMap, updateScriptHash)
import Data.Bifunctor (second)
import Language.Marlowe.Scripts (marloweValidatorBytes, marloweValidatorHash,
                                 rolePayoutValidatorHash)
import PlutusLedgerApi.V2 (Credential (PubKeyCredential, ScriptCredential), ExBudget (ExBudget),
                           Extended (NegInf, PosInf), Interval (Interval), LowerBound (LowerBound),
                           ScriptContext (ScriptContext, scriptContextPurpose, scriptContextTxInfo),
                           ScriptHash, ScriptPurpose (Spending), SerialisedScript,
                           TxInfo (TxInfo, txInfoDCert, txInfoData, txInfoFee, txInfoId, txInfoInputs, txInfoMint, txInfoOutputs, txInfoRedeemers, txInfoReferenceInputs, txInfoSignatories, txInfoValidRange, txInfoWdrl),
                           TxOutRef (TxOutRef), UpperBound (UpperBound))

import PlutusTx.AssocMap qualified as AM (empty)


-- | The serialised Marlowe semantics validator.
validatorBytes :: SerialisedScript
validatorBytes = marloweValidatorBytes


-- | The script hash for the Marlowe semantics validator.
validatorHash :: ScriptHash
validatorHash = marloweValidatorHash


-- | The benchmark cases for the Marlowe semantics validator.
benchmarks :: IO (Either String [Benchmark])
benchmarks =
  let
    update benchmark@Benchmark{..} =
      benchmark {
        bScriptContext =
          updateScriptHash
            "2ed2631dbb277c84334453c5c437b86325d371f0835a28b910a91a6e"
            marloweValidatorHash
          $ updateScriptHash
            "e165610232235bbbbeff5b998b233daae42979dec92a6722d9cda989"
            rolePayoutValidatorHash
            bScriptContext
      }
  in
    second (update <$>) <$> readBenchmarks "semantics"


-- | An example benchmark for the Marlowe semantics validator.
exampleBenchmark :: Benchmark
exampleBenchmark =
  let
    txInfoInputs =
      [
        makeInput
          "04688f43cf473ddcc27aeef0c9ccae1d7efb97d83a1dfc946d2ab36ba91a91b9" 0
          (PubKeyCredential "0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07")
          (lovelace 29965798056)
          Nothing
          Nothing
      , makeInput
          "04688f43cf473ddcc27aeef0c9ccae1d7efb97d83a1dfc946d2ab36ba91a91b9" 1
          (ScriptCredential "e165610232235bbbbeff5b998b233daae42979dec92a6722d9cda989")
          (lovelace 2000000)
          (Just "665baf0f5d371ff18587ead2332a81aefa73d169c66970faafc759ec43208d4f")
          Nothing
      ]
    txInfoReferenceInputs =
      [
        makeInput
          "9a8a6f387a3330b4141e1cb019380b9ac5c72151c0abc52aa4266245d3c555cd" 1
          (PubKeyCredential "f685ca45a4c8c07dd592ba1609690b56fdb0b81cef9440345de947f1")
          (lovelace 12899830)
          Nothing
          (Just "e165610232235bbbbeff5b998b233daae42979dec92a6722d9cda989")
      ]
    txInfoOutputs =
      [
        makeOutput
          (PubKeyCredential "0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07")
          (lovelace 29965369677)
          Nothing
          Nothing
      , makeOutput
          (PubKeyCredential "0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07")
          (lovelace 2000000)
          Nothing
          Nothing
      ]
    txInfoFee = lovelace 428379
    txInfoMint = mempty
    txInfoDCert = mempty
    txInfoWdrl = AM.empty
    txInfoValidRange = Interval (LowerBound NegInf False) (UpperBound PosInf False)
    txInfoSignatories = ["e165610232235bbbbeff5b998b233daae42979dec92a6722d9cda989"]
    txInfoRedeemers = makeRedeemerMap scriptContextPurpose "80"
    txInfoData =
      makeDatumMap
        "665baf0f5d371ff18587ead2332a81aefa73d169c66970faafc759ec43208d4f"
        "d8799fd8799f40ffd8799fa1d8799fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd8799f4040ffff1a001e8480a0a000ffd87c9f9fd8799fd87b9fd9050380ffd87980ffff01d87980ffff"
    txInfoId = "4e16f03a5533f22adbc5097a07077f3b708b1bf74b42e6b2938dd2d4156207f0"
    scriptContextTxInfo = TxInfo{..}
    scriptContextPurpose =
      Spending $ TxOutRef "04688f43cf473ddcc27aeef0c9ccae1d7efb97d83a1dfc946d2ab36ba91a91b9" 1
  in
    makeBenchmark
      (makeBuiltinData "d8799fd8799f40ffd8799fa1d8799fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd8799f4040ffff1a001e8480a0a000ffd87c9f9fd8799fd87b9fd9050380ffd87980ffff01d87980ffff")
      (makeBuiltinData "80")
      ScriptContext{..}
      (Just $ ExBudget 3147810 832740336)
