-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

module PlutusBenchmark.Marlowe.Semantics
  ( validatorBytes
  , validatorHash
  , exampleBenchmark
  , writeUPLC
  ) where

import PlutusBenchmark.Marlowe.BenchUtil (writeFlatUPLC)
import PlutusBenchmark.Marlowe.Scripts.Semantics
  ( marloweValidator
  , marloweValidatorBytes
  , marloweValidatorHash
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
import PlutusLedgerApi.V1.Value (TokenName (TokenName))
import PlutusLedgerApi.V2
  ( Credential (PubKeyCredential, ScriptCredential)
  , CurrencySymbol (..)
  , ExBudget (ExBudget)
  , Extended (..)
  , Interval (Interval)
  , LowerBound (LowerBound)
  , ScriptContext (ScriptContext, scriptContextPurpose, scriptContextTxInfo)
  , ScriptHash
  , ScriptPurpose (Spending)
  , SerialisedScript
  , TxInfo (TxInfo, txInfoDCert, txInfoData, txInfoFee, txInfoId, txInfoInputs, txInfoMint, txInfoOutputs, txInfoRedeemers, txInfoReferenceInputs, txInfoSignatories, txInfoValidRange, txInfoWdrl)
  , TxOutRef (TxOutRef)
  , UpperBound (UpperBound)
  , singleton
  )
import PlutusTx.AssocMap qualified as AM (empty, unionWith)

-- | The serialised Marlowe semantics validator.
validatorBytes :: SerialisedScript
validatorBytes = marloweValidatorBytes

-- | The script hash for the Marlowe semantics validator.
validatorHash :: ScriptHash
validatorHash = marloweValidatorHash

-- | Write flat UPLC for a benchmark.
writeUPLC
  :: FilePath
  -> Benchmark
  -> IO ()
writeUPLC = writeFlatUPLC marloweValidator

{-# DEPRECATED exampleBenchmark "Experimental, not thoroughly tested." #-}

-- | An example benchmark for the Marlowe semantics validator.
exampleBenchmark :: Benchmark
exampleBenchmark =
  let
    txInfoInputs =
      [ makeInput
          "4a6808d88ffbceadf2bd86897bbacb9ee04131c9ccd56c998bfbcb65c0f3f471"
          0
          (PubKeyCredential "0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07")
          (lovelace 847996471)
          Nothing
          Nothing
      , makeInput
          "4a6808d88ffbceadf2bd86897bbacb9ee04131c9ccd56c998bfbcb65c0f3f471"
          1
          (ScriptCredential "626424dba5741cb1f0a3cab8643da59ffccba351495c4257f9ec3689")
          (lovelace 75000000)
          (Just "b4c9d042bd5fbb14431ad65769e21ccf132fd57e0c62f776dcb12961c44bd663")
          Nothing
      , makeInput
          "db85a19c081d0beca1a63399c88fe96e64f1782699461f64e52d4cb2e26a2050"
          1
          (PubKeyCredential "0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07")
          ( singleton
              (CurrencySymbol "8bb3b343d8e404472337966a722150048c768d0a92a9813596c5338d")
              (TokenName "Globe")
              1
              <> lovelace 2000000
          )
          Nothing
          Nothing
      ]
    txInfoReferenceInputs = []
    txInfoOutputs =
      [ makeOutput
          (PubKeyCredential "0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07")
          (lovelace 847801537)
          Nothing
          Nothing
      , makeOutput
          (ScriptCredential "626424dba5741cb1f0a3cab8643da59ffccba351495c4257f9ec3689")
          (lovelace 75000000)
          (Just "290c87ba567afe9e3eba9309c37ad993d2be7dbcbfcfaeff09f0009b3d5b2ed9")
          Nothing
      , makeOutput
          (PubKeyCredential "0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07")
          ( singleton
              (CurrencySymbol "8bb3b343d8e404472337966a722150048c768d0a92a9813596c5338d")
              (TokenName "Globe")
              1
              <> lovelace 1030090
          )
          Nothing
          Nothing
      ]
    txInfoFee = lovelace 1164844
    txInfoMint = mempty
    txInfoDCert = mempty
    txInfoWdrl = AM.empty
    txInfoValidRange =
      Interval
        (LowerBound (Finite 1684449918000) True)
        (UpperBound (Finite 1684450278000) False)
    txInfoSignatories = ["0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07"]
    txInfoRedeemers =
      makeRedeemerMap
        scriptContextPurpose
        "9fd8799fd87a9fd8799f51466f756e6420476c6f626520546f6b656ed87a9f45476c6f6265ffff00ffffff"
    txInfoData =
      AM.unionWith
        const
        ( makeDatumMap
            "b4c9d042bd5fbb14431ad65769e21ccf132fd57e0c62f776dcb12961c44bd663"
            "d8799fd8799f581c8bb3b343d8e404472337966a722150048c768d0a92a9813596c5338dffd8799fa1d8799fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd8799f4040ffff1a047868c0a0a001ffd87c9f9fd8799fd87a9fd8799f51466f756e6420476c6f626520546f6b656ed87a9f45476c6f6265ffff9fd8799f0000ffffffd87c9f9fd8799fd87a9fd8799f50466f756e64205377616e20546f6b656ed87a9f445377616effff9fd8799f0000ffffffd87c9f9fd8799fd87a9fd8799f56466f756e64204265617247617264656e20546f6b656ed87a9f4a4265617247617264656effff9fd8799f0000ffffffd87a9fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd87a9fd87a9f45476c6f6265ffffd8799f4040ffd87a9f1a017d7840ffd87a9fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd87a9fd87a9f445377616effffd8799f4040ffd87a9f1a017d7840ffd87a9fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd87a9fd87a9f4a4265617247617264656effffd8799f4040ffd87a9f1a017d7840ffd87980ffffffffff1b0000018831ac75f0d87980ffffff1b0000018831758770d87980ffffff1b00000188313e98f0d87980ffff"
        )
        ( makeDatumMap
            "290c87ba567afe9e3eba9309c37ad993d2be7dbcbfcfaeff09f0009b3d5b2ed9"
            "d8799fd8799f581c8bb3b343d8e404472337966a722150048c768d0a92a9813596c5338dffd8799fa1d8799fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd8799f4040ffff1a047868c0a1d8799f51466f756e6420476c6f626520546f6b656ed87a9f45476c6f6265ffff00a01b000001883109fc30ffd87c9f9fd8799fd87a9fd8799f50466f756e64205377616e20546f6b656ed87a9f445377616effff9fd8799f0000ffffffd87c9f9fd8799fd87a9fd8799f56466f756e64204265617247617264656e20546f6b656ed87a9f4a4265617247617264656effff9fd8799f0000ffffffd87a9fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd87a9fd87a9f45476c6f6265ffffd8799f4040ffd87a9f1a017d7840ffd87a9fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd87a9fd87a9f445377616effffd8799f4040ffd87a9f1a017d7840ffd87a9fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd87a9fd87a9f4a4265617247617264656effffd8799f4040ffd87a9f1a017d7840ffd87980ffffffffff1b0000018831ac75f0d87980ffffff1b0000018831758770d87980ffff"
        )
    txInfoId = "b5b18fb63795bada186cc4b3876cb9a924467f0d64984c84886b58f7a907f8db"
    scriptContextTxInfo = TxInfo {..}
    scriptContextPurpose =
      Spending $ TxOutRef "04688f43cf473ddcc27aeef0c9ccae1d7efb97d83a1dfc946d2ab36ba91a91b9" 1
   in
    makeBenchmark
      ( makeBuiltinData
          "d8799fd8799f581c8bb3b343d8e404472337966a722150048c768d0a92a9813596c5338dffd8799fa1d8799fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd8799f4040ffff1a047868c0a0a001ffd87c9f9fd8799fd87a9fd8799f51466f756e6420476c6f626520546f6b656ed87a9f45476c6f6265ffff9fd8799f0000ffffffd87c9f9fd8799fd87a9fd8799f50466f756e64205377616e20546f6b656ed87a9f445377616effff9fd8799f0000ffffffd87c9f9fd8799fd87a9fd8799f56466f756e64204265617247617264656e20546f6b656ed87a9f4a4265617247617264656effff9fd8799f0000ffffffd87a9fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd87a9fd87a9f45476c6f6265ffffd8799f4040ffd87a9f1a017d7840ffd87a9fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd87a9fd87a9f445377616effffd8799f4040ffd87a9f1a017d7840ffd87a9fd8799fd87980d8799fd8799f581c0a11b0c7e25dc5d9c63171bdf39d9741b901dc903e12b4e162348e07ffd87a80ffffd87a9fd87a9f4a4265617247617264656effffd8799f4040ffd87a9f1a017d7840ffd87980ffffffffff1b0000018831ac75f0d87980ffffff1b0000018831758770d87980ffffff1b00000188313e98f0d87980ffff"
      )
      ( makeBuiltinData
          "9fd8799fd87a9fd8799f51466f756e6420476c6f626520546f6b656ed87a9f45476c6f6265ffff00ffffff"
      )
      ScriptContext {..}
      (Just $ ExBudget 4808532 1297175159)
