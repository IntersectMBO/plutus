-- | Golden cases for Cardan Open Oracle Protocol scripts.
module Main (main) where

import Test.Tasty
import Test.Tasty.Extras (runTestNested, testNestedGhc)

import PlutusLedgerApi.V2 (BuiltinData, Datum (..), Redeemer (..), ToData, toBuiltinData)

import PlutusTx.Code (CompiledCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Test (unsafeApplyCodeN)
import PlutusTx.Test qualified as Tx

import PlutusBenchmark.Coop.Scripts qualified as Scripts
import PlutusBenchmark.Coop.TestContext
import PlutusBenchmark.Coop.Types

liftCodeDefAsData :: ToData a => a -> CompiledCode BuiltinData
liftCodeDefAsData = liftCodeDef . toBuiltinData

allTests :: TestTree
allTests =
  runTestNested ["coop", "test"] $
    pure $
      testNestedGhc
        [ Tx.goldenEvalCekCatchBudget "mustBurnOwnSingleton" $
            unsafeApplyCodeN
              Scripts.fsV
              (liftCodeDef $ Datum $ toBuiltinData ())
              (liftCodeDefAsData ())
              (liftCodeDefAsData correctMustBurnOwnSingletonValueContext)
        , Tx.goldenEvalCekCatchBudget "certMpMinting" $
            unsafeApplyCodeN
              Scripts.certMp
              (liftCodeDef certMpParams)
              (liftCodeDefAsData $ Redeemer $ toBuiltinData CertMpMint)
              (liftCodeDefAsData correctCertMpMintingContext)
        , Tx.goldenEvalCekCatchBudget "certMpBurning" $
            unsafeApplyCodeN
              Scripts.certMp
              (liftCodeDef certMpParams)
              (liftCodeDefAsData $ Redeemer $ toBuiltinData CertMpBurn)
              (liftCodeDefAsData correctCertMpBurningContext)
        , Tx.goldenEvalCekCatchBudget "fsMpMinting" $
            unsafeApplyCodeN
              Scripts.fsMp
              (liftCodeDef fsMpParams)
              (liftCodeDefAsData $ Redeemer $ toBuiltinData FsMpMint)
              (liftCodeDefAsData correctFsMpMintingContext)
        , Tx.goldenEvalCekCatchBudget "fsMpBurning" $
            unsafeApplyCodeN
              Scripts.fsMp
              (liftCodeDef fsMpParams)
              (liftCodeDefAsData $ Redeemer $ toBuiltinData FsMpBurn)
              (liftCodeDefAsData correctFsMpBurningContext)
        , Tx.goldenEvalCekCatchBudget "authMpMinting" $
            unsafeApplyCodeN
              Scripts.authMp
              (liftCodeDef authMpParams)
              (liftCodeDefAsData $ Redeemer $ toBuiltinData AuthMpMint)
              (liftCodeDefAsData correctAuthMpMintingContext)
        , Tx.goldenEvalCekCatchBudget "authMpBurning" $
            unsafeApplyCodeN
              Scripts.authMp
              (liftCodeDef authMpParams)
              (liftCodeDefAsData $ Redeemer $ toBuiltinData AuthMpBurn)
              (liftCodeDefAsData correctAuthMpBurningContext)
        ]

main :: IO ()
main = defaultMain allTests
