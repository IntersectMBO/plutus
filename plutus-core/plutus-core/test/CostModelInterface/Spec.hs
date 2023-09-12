-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
module CostModelInterface.Spec (test_costModelInterface) where

import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.MachineParameters

import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts

import Data.Aeson
import Data.ByteString.Lazy qualified as BSL
import Data.Either
import Data.Either.Extras
import Data.Map qualified as Map
import Data.Maybe
import Data.Text qualified as Text
import Instances.TH.Lift ()
import Language.Haskell.TH.Syntax qualified as TH
import Prettyprinter
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import TH.RelativePaths

{- Note [Testing the expected ledger cost model parameters]
The ledger is going to call us with a particular 'CostModelParams'. This will be originally derived from the model
that we provide, but there's opportunity for things to move out of sync:
1. The ledger could make a mistake and pass us the wrong parameters (e.g. mis-spelled)
2. We could change how the loading works so that what they pass us ceases to work properly.

So it's sensible to have some regression tests.

We can't just test against our own 'defaultCostModelParams', since in the case of error 2 that would
*also* change, so we instead need to have a checked-in version of the parameters.
-}

-- | A checked-in of the default cost model params, frozen by calling 'CostModelInterface.extractCostModelParams'
-- See Note [Testing the expected ledger cost model parameters]
ledgerParamsBS :: BSL.ByteString
ledgerParamsBS = $(TH.lift =<< qReadFileLBS ("plutus-core" </> "test" </> "CostModelInterface" </> "defaultCostModelParams.json"))

type CekCostModel = CostModel CekMachineCosts BuiltinCostModel

-- Just for testing
randomCekCosts :: CekMachineCosts
randomCekCosts =
    CekMachineCostsBase
                    { cekStartupCost = pure $ ExBudget 2342 234321
                    , cekVarCost     = pure $ ExBudget 12312 56545
                    , cekConstCost   = pure $ ExBudget 23490290838 2323423
                    , cekLamCost     = pure $ ExBudget 0 712127381
                    , cekDelayCost   = pure $ ExBudget 999 7777
                    , cekForceCost   = pure $ ExBudget 1028234 0
                    , cekApplyCost   = pure $ ExBudget 324628348 8273
                    , cekBuiltinCost = pure $ ExBudget 4 4
                    , cekConstrCost  = pure $ ExBudget 8 100000
                    , cekCaseCost    = pure $ ExBudget 3324234 555
                    }

cekVarCostCpuKey :: Text.Text
cekVarCostCpuKey = "cekVarCost-exBudgetCPU"  -- This is the result of flatten . toJSON

randomCekCostModel :: CekCostModel
randomCekCostModel = CostModel randomCekCosts defaultBuiltinCostModel

-- Tests

-- | Extract the params from a cost model and return them, failing if it doesn't work
extractParams :: CekCostModel -> IO CostModelParams
extractParams model = do
  case extractCostModelParams model of
    Nothing -> assertFailure "extractCostModelParams failed"
    Just p  -> pure p

-- | Extract some params from a cost model and return the updated version, failing if it doesn't work
applyParams :: CekCostModel -> CostModelParams -> IO CekCostModel
applyParams model params = fromRightM (assertFailure . show . pretty) $ applyCostModelParams model params
-- | Just check that extraction works.
testExtraction :: CekCostModel -> IO ()
testExtraction model = do
  _extracted <- extractParams model  -- We're not going to use this but it may still fail.
  pure ()

-- Update a model with its own parameters and check that we get the same model back
testSelfUpdate :: CekCostModel -> IO ()
testSelfUpdate model = do
  params <- extractParams model
  updated <- applyParams model params
  updated @?= model

-- Update a model with its no parameters and check that we get the same model back
testUpdateEmpty :: CekCostModel -> IO ()
testUpdateEmpty model = do
  updated <- applyParams model mempty
  updated @?= model

-- Update a model model1 with the parameters from model2 and check that we get model2
testOverwrite :: CekCostModel -> CekCostModel -> IO ()
testOverwrite model1 model2 = do
  params <- extractParams model2
  updated <- applyParams model1 params
  updated @?= model2

-- Update a model with its own params with an extra entry.  This is NOT OK.
testSelfUpdateWithExtraEntry :: CekCostModel -> IO ()
testSelfUpdateWithExtraEntry model =
    do
      params <- extractParams model
      let params' = Map.insert "XYZ" 123 params
          mModel = applyCostModelParams model params'
      assertBool "Superfluous costparam was not caught." $ isLeft mModel

-- Update a model with its own params with an entry deleted: this should
-- be OK because the original member of the model will still be there.
testSelfUpdateWithMissingEntry :: CekCostModel -> IO ()
testSelfUpdateWithMissingEntry model =
    do
      params <- extractParams model
      assertBool (Text.unpack cekVarCostCpuKey ++ " not found in params") (Map.member cekVarCostCpuKey params)
      let params' = Map.delete cekVarCostCpuKey params
      model' <- applyParams model params'
      model' @?= model

-- Update a model with the params from another model with an entry
-- deleted.  The result should be different from both of the original models.
testOtherUpdateWithMissingEntry :: CekCostModel -> CekCostModel -> IO ()
testOtherUpdateWithMissingEntry model1 model2 =
    do
      params2 <- extractParams model2
      assertBool (Text.unpack cekVarCostCpuKey ++ " not found in params") (Map.member cekVarCostCpuKey params2)
      let params2' = Map.delete cekVarCostCpuKey params2
      assertBool (Text.unpack cekVarCostCpuKey ++ " still in params") (not (Map.member cekVarCostCpuKey params2'))
      assertBool "params are the same" (params2 /= params2')
      model1' <- applyParams model1 params2'
      assertBool "The updated model is the same as the other model" (model1' /= model2)
      assertBool "The updated model is the same as the original"    (model1' /= model1)

-- Update a model with the params from another and then check that
-- extraction returns the same params.
testExtractAfterUpdate ::  CekCostModel -> CekCostModel -> IO ()
testExtractAfterUpdate model1 model2 =
    do
      params <- extractParams model2
      updated <- applyParams model1 params
      params' <- extractParams updated
      params' @?= params

-- | Test that we can deserialise the default ledger params
testDeserialise :: IO ()
testDeserialise = assertBool "Failed to decode default ledger cost params" $
    isJust $ decode @CostModelParams ledgerParamsBS

-- | Test that we can apply the ledger params to our cost model
testApply :: IO ()
testApply = do
    let decodedParams = fromJust $ decode @CostModelParams ledgerParamsBS
    assertBool "Failed to load the ledger cost params into the our cost model" $
        isRight $ applyCostModelParams defaultCekCostModel decodedParams

-- | Test to catch a mispelled/missing param.
-- A parameter with that name exists in the ledger params but is missing from the cost model, and that is an error.
testMispelled :: IO ()
testMispelled = do
    let params = fromJust $ decode @CostModelParams ledgerParamsBS
        (cekVarCostValueM, paramsReducted) = deleteLookup cekVarCostCpuKey params
        paramsMispelled = Map.insert cekVarCostCpuKeyMispelled (fromJust cekVarCostValueM) paramsReducted
    assertBool "Failed to catch mispelled cost param" $
        isLeft $ applyCostModelParams defaultCekCostModel paramsMispelled
  where
      cekVarCostCpuKeyMispelled = "cekVarCost--exBudgetCPU"
      deleteLookup = Map.updateLookupWithKey (const $ const Nothing)

test_costModelInterface :: TestTree
test_costModelInterface =
    testGroup "cost model interface tests"
       [ testGroup "extractCostModelParams works"
             [ testCase "defaultCekCostModel" $ testExtraction defaultCekCostModel
             , testCase "randomCekCostModel"  $ testExtraction randomCekCostModel
             ]
       , testGroup "self-update is identity"
             [ testCase "defaultCekCostModel <- defaultCekCostModel" $ testSelfUpdate defaultCekCostModel
             , testCase "randomCekCostModel  <- randomCekCostModel"  $ testSelfUpdate randomCekCostModel
             ]
       , testGroup "update-empty is identity"
             [ testCase "defaultCekCostModel <- defaultCekCostModel" $ testUpdateEmpty defaultCekCostModel
             , testCase "randomCekCostModel  <- randomCekCostModel"  $ testUpdateEmpty randomCekCostModel
             ]
       , testGroup "overwriting works"
             [ testCase "defaultCekCostModel <- randomCekCostModel"  $ testOverwrite defaultCekCostModel randomCekCostModel
             , testCase "randomCekCostModel  <- defaultCekCostModel" $ testOverwrite randomCekCostModel  defaultCekCostModel
             ]
       , testGroup "superfluous entry in params is NOT OK in self-update"
             [ testCase "defaultCekCostModel" $ testSelfUpdateWithExtraEntry defaultCekCostModel
             , testCase "randomCekCostModel"  $ testSelfUpdateWithExtraEntry randomCekCostModel
             ]
       , testGroup "missing entry in params is OK in self-update"
             [ testCase "defaultCekCostModel" $ testSelfUpdateWithMissingEntry defaultCekCostModel
             , testCase "randomCekCostModel"  $ testSelfUpdateWithMissingEntry randomCekCostModel
             ]
       , testGroup "missing entry in update of different model"
             [ testCase "defaultCekCostModel" $ testOtherUpdateWithMissingEntry defaultCekCostModel randomCekCostModel
             , testCase "randomCekCostModel"  $ testOtherUpdateWithMissingEntry randomCekCostModel defaultCekCostModel
             ]
       , testGroup "extract after apply is identity"
             [ testCase "defaultCekCostModel <- defaultCekCostModel" $ testExtractAfterUpdate defaultCekCostModel defaultCekCostModel
             , testCase "randomCekCostModel  <- randomCekCostModel"  $ testExtractAfterUpdate randomCekCostModel  randomCekCostModel
             , testCase "randomCekCostModel  <- defaultCekCostModel" $ testExtractAfterUpdate randomCekCostModel  defaultCekCostModel
             , testCase "defaultCekCostModel <- randomCekCostModel"  $ testExtractAfterUpdate defaultCekCostModel randomCekCostModel
             ]
       , testGroup "default ledger params"
             [ testCase "default ledger params deserialize" testDeserialise
             , testCase "default ledger params can be applied to default cost model" testApply
             , testCase "mispelled param in ledger params " testMispelled
             ]
     ]

