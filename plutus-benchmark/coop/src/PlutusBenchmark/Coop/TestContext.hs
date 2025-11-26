{-# LANGUAGE OverloadedStrings #-}

module PlutusBenchmark.Coop.TestContext
  ( certMpParams
  , fsMpParams
  , authMpParams
  , correctMustBurnOwnSingletonValueContext
  , correctCertMpMintingContext
  , correctCertMpBurningContext
  , correctFsMpMintingContext
  , correctFsMpBurningContext
  , correctAuthMpMintingContext
  , correctAuthMpBurningContext
  ) where

import PlutusLedgerApi.V1.Address (scriptHashAddress)
import PlutusLedgerApi.V1.Value (AssetClass, CurrencySymbol (..), TokenName (..), assetClass)
import PlutusLedgerApi.V2 (Address, ScriptContext, ScriptHash (..))

import Test.QuickCheck.Gen (Gen (unGen))
import Test.QuickCheck.Random (mkQCGen)

import PlutusBenchmark.Coop.Gen qualified as CG
import PlutusBenchmark.Coop.Types

-- Some Constants Used for Script Context --
coopAc :: AssetClass
coopAc = assetClass (CurrencySymbol "$COOP CurrencySymbol") (TokenName "$COOP TokenName")

aaAc :: AssetClass
aaAc = assetClass (CurrencySymbol "$AA CurrencySymbol") (TokenName "$AA TokenName")

certCs :: CurrencySymbol
certCs = CurrencySymbol "cert-policy- hash"

authCs :: CurrencySymbol
authCs = CurrencySymbol "auth-policy- hash"

fsCs :: CurrencySymbol
fsCs = CurrencySymbol "fs-policy- hash"

certVAddr :: Address
certVAddr = scriptHashAddress . ScriptHash $ "@CertV hash"

fsVAddr :: Address
fsVAddr = scriptHashAddress . ScriptHash $ "@FsV hash"

aaQ :: Integer
aaQ = 42

certMpParams :: CertMpParams
certMpParams = CertMpParams aaAc aaQ certVAddr

fsMpParams :: FsMpParams
fsMpParams = FsMpParams coopAc fsVAddr (AuthParams authCs certCs)

authMpParams :: AuthMpParams
authMpParams = AuthMpParams aaAc aaQ

runGen :: Gen a -> a
runGen g = unGen g (mkQCGen 1) 1

correctMustBurnOwnSingletonValueContext :: ScriptContext
correctMustBurnOwnSingletonValueContext = runGen CG.genCorrectMustBurnOwnSingletonValueCtx

correctCertMpMintingContext :: ScriptContext
correctCertMpMintingContext = runGen $ CG.genCorrectCertMpMintingCtx certMpParams certCs

correctCertMpBurningContext :: ScriptContext
correctCertMpBurningContext = runGen $ CG.genCertRdmrAc >>= CG.genCorrectCertMpBurningCtx certMpParams certCs

correctFsMpMintingContext :: ScriptContext
correctFsMpMintingContext = runGen $ CG.genCorrectFsMpMintingCtx fsMpParams fsCs

correctFsMpBurningContext :: ScriptContext
correctFsMpBurningContext = runGen $ CG.genCorrectFsMpBurningCtx fsMpParams fsCs

correctAuthMpMintingContext :: ScriptContext
correctAuthMpMintingContext = runGen $ CG.genCorrectAuthMpMintingCtx authMpParams authCs

correctAuthMpBurningContext :: ScriptContext
correctAuthMpBurningContext = runGen $ CG.genCorrectAuthMpBurningCtx authCs
