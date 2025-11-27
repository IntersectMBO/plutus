{-# LANGUAGE OverloadedStrings #-}

module PlutusBenchmark.Marlowe.RolePayout
  ( benchmarks
  , validatorBytes
  , validatorHash
  , exampleBenchmark
  , writeUPLC
  ) where

import Data.Bifunctor (second)
import PlutusBenchmark.Marlowe.BenchUtil (readBenchmarks, updateScriptHash, writeFlatUPLC)
import PlutusBenchmark.Marlowe.Scripts.RolePayout
  ( rolePayoutValidator
  , rolePayoutValidatorBytes
  , rolePayoutValidatorHash
  )
import PlutusBenchmark.Marlowe.Types (Benchmark (..), makeBenchmark)
import PlutusBenchmark.Marlowe.Util
  ( lovelace
  , makeBuiltinData
  , makeDatumMap
  , makeInput
  , makeOutput
  , makeRedeemerMap
  )
import PlutusLedgerApi.V2
  ( Credential (PubKeyCredential, ScriptCredential)
  , CurrencySymbol (..)
  , ExBudget (ExBudget)
  , Extended (NegInf, PosInf)
  , Interval (Interval)
  , LowerBound (LowerBound)
  , ScriptContext (ScriptContext, scriptContextPurpose, scriptContextTxInfo)
  , ScriptHash
  , ScriptPurpose (Spending)
  , SerialisedScript
  , TxInfo (..)
  , TxOutRef (TxOutRef)
  , UpperBound (UpperBound)
  , singleton
  )

import PlutusLedgerApi.V1.Value (TokenName (TokenName))
import PlutusTx.AssocMap qualified as AM (empty)

-- | Write a flat UPLC file for a benchmark.
writeUPLC :: FilePath -> Benchmark -> IO ()
writeUPLC = writeFlatUPLC rolePayoutValidator

-- | The serialised Marlowe role-payout validator.
validatorBytes :: SerialisedScript
validatorBytes = rolePayoutValidatorBytes

-- | The hash for the Marlowe role-payout validator.
validatorHash :: ScriptHash
validatorHash = rolePayoutValidatorHash

-- | The benchmark cases for the Marlowe role-payout validator.
benchmarks :: IO (Either String [Benchmark])
benchmarks =
  second (rescript <$>) <$> readBenchmarks "marlowe/scripts/rolepayout"

-- | Revise the validator hashes in the benchmark's script context.
rescript :: Benchmark -> Benchmark
rescript benchmark@Benchmark {..} =
  benchmark
    { bScriptContext =
        updateScriptHash
          "e165610232235bbbbeff5b998b233daae42979dec92a6722d9cda989"
          rolePayoutValidatorHash
          bScriptContext
    }

{-# DEPRECATED exampleBenchmark "Experimental, not thoroughly tested." #-}

-- | An example benchmark for the Marlowe role-payout validator.
exampleBenchmark :: Benchmark
exampleBenchmark =
  let
    txInfoInputs =
      [ makeInput
          "6ca85e35c485181d54b4092a49ed9fec93a3f21b603c68cbca741ec27de318cf"
          0
          (PubKeyCredential "5411f58036fcd19b79cc51539233698dd9b86c2e53d132675b152ce8")
          (lovelace 1008173101)
          Nothing
          Nothing
      , makeInput
          "6ca85e35c485181d54b4092a49ed9fec93a3f21b603c68cbca741ec27de318cf"
          1
          (PubKeyCredential "5411f58036fcd19b79cc51539233698dd9b86c2e53d132675b152ce8")
          ( singleton
              (CurrencySymbol "d768a767450e9ffa2d68ae61e8476fb6267884e0477d7fd19703f9d8")
              (TokenName "Seller")
              1
              <> lovelace 1034400
          )
          Nothing
          Nothing
      , makeInput
          "ef6a9ef1b84bef3dad5e12d9bf128765595be4a92da45bda2599dc7fae7e2397"
          1
          (ScriptCredential "e165610232235bbbbeff5b998b233daae42979dec92a6722d9cda989")
          (lovelace 75000000)
          (Just "95de9e2c3bface3de5739c0bd5197f0864315c1819c52783afb9b2ce075215f5")
          Nothing
      ]
    txInfoReferenceInputs =
      [ makeInput
          "9a8a6f387a3330b4141e1cb019380b9ac5c72151c0abc52aa4266245d3c555cd"
          1
          (PubKeyCredential "f685ca45a4c8c07dd592ba1609690b56fdb0b81cef9440345de947f1")
          (lovelace 12899830)
          Nothing
          (Just "e165610232235bbbbeff5b998b233daae42979dec92a6722d9cda989")
      ]
    txInfoOutputs =
      [ makeOutput
          (PubKeyCredential "5411f58036fcd19b79cc51539233698dd9b86c2e53d132675b152ce8")
          (lovelace 1082841547)
          Nothing
          Nothing
      , makeOutput
          (PubKeyCredential "5411f58036fcd19b79cc51539233698dd9b86c2e53d132675b152ce8")
          ( singleton
              (CurrencySymbol "d768a767450e9ffa2d68ae61e8476fb6267884e0477d7fd19703f9d8")
              (TokenName "Seller")
              1
              <> lovelace 1034400
          )
          Nothing
          Nothing
      ]
    txInfoFee = lovelace 331554
    txInfoMint = mempty
    txInfoDCert = mempty
    txInfoWdrl = AM.empty
    txInfoValidRange = Interval (LowerBound NegInf False) (UpperBound PosInf False)
    txInfoSignatories = ["5411f58036fcd19b79cc51539233698dd9b86c2e53d132675b152ce8"]
    txInfoRedeemers = makeRedeemerMap scriptContextPurpose "d87980"
    txInfoData =
      makeDatumMap
        "95de9e2c3bface3de5739c0bd5197f0864315c1819c52783afb9b2ce075215f5"
        "d8799f581cd768a767450e9ffa2d68ae61e8476fb6267884e0477d7fd19703f9d84653656c6c6572ff"
    txInfoId = "4e16f03a5533f22adbc5097a07077f3b708b1bf74b42e6b2938dd2d4156207f0"
    scriptContextTxInfo = TxInfo {..}
    scriptContextPurpose =
      Spending $ TxOutRef "ef6a9ef1b84bef3dad5e12d9bf128765595be4a92da45bda2599dc7fae7e2397" 1
   in
    makeBenchmark
      ( makeBuiltinData
          "d8799f581cd768a767450e9ffa2d68ae61e8476fb6267884e0477d7fd19703f9d84653656c6c6572ff"
      )
      (makeBuiltinData "d87980")
      ScriptContext {..}
      (Just $ ExBudget 477988519 1726844)
