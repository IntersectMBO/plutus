{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CostModelInterface.Spec (test_costModelInterface) where

import           PlutusCore
import           PlutusCore.Evaluation.Machine.CostModelInterface
import           PlutusCore.Evaluation.Machine.ExBudget
import           PlutusCore.Evaluation.Machine.MachineParameters

import qualified Data.Map                                         as Map
import qualified Data.Text                                        as Text
import           Test.Tasty
import           Test.Tasty.HUnit

type CekCostModel = CostModel CekMachineCosts

-- Just for testing
randomCekCosts :: CekMachineCosts
randomCekCosts =
    CekMachineCosts { cekStartupCost = ExBudget 2342 234321
                    , cekStepCost    = ExBudget 12312 56545
                    }

cekStepCostCpuKey :: Text.Text
cekStepCostCpuKey = "cek_step_cost-_ex_budget_cpu"  -- This is the result of flatten . camelToSnake

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
applyParams model params = do
  case applyCostModelParams model params of
    Nothing     -> assertFailure "applyCostModelParams failed"
    Just model' -> pure model'

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

-- Update a model model1 with the parameters from model2 and check that we get model2
testOverwrite :: CekCostModel -> CekCostModel -> IO ()
testOverwrite model1 model2 = do
  params <- extractParams model2
  updated <- applyParams model1 params
  updated @?= model2

-- Update a model with its own params with an extra entry.  This is OK:
-- 'fromJSON' will successfully decode anything that contains sufficient
-- information to construct a result of the expected type, but extra stuff can
-- be present as well.
testSelfUpdateWithExtraEntry :: CekCostModel -> IO ()
testSelfUpdateWithExtraEntry model =
    do
      params <- extractParams model
      let params' = Map.insert "XYZ" 123 params
      model' <- applyParams model params'
      model' @?= model

-- Update a model with its own params with an entry deleted: this should
-- be OK because the original member of the model will still be there.
testSelfUpdateWithMissingEntry :: CekCostModel -> IO ()
testSelfUpdateWithMissingEntry model =
    do
      params <- extractParams model
      assertBool "CekStepCost not found in params" (Map.member cekStepCostCpuKey params)
      let params' = Map.delete cekStepCostCpuKey params
      model' <- applyParams model params'
      model' @?= model

-- Update a model with the params from another model with an entry
-- deleted.  The result should be different from both of the original models.
testOtherUpdateWithMissingEntry :: CekCostModel -> CekCostModel -> IO ()
testOtherUpdateWithMissingEntry model1 model2 =
    do
      params2 <- extractParams model2
      assertBool "CekStepCost not found in params" (Map.member cekStepCostCpuKey params2)
      let params2' = Map.delete cekStepCostCpuKey params2
      assertBool "CekStepCost still in params" (not (Map.member cekStepCostCpuKey params2'))
      assertBool "params are the same" (params2 /= params2')
      model1' <- applyParams model1 params2'
      assertBool "The updated model is the same as the other model" (model1' /= model2)
      assertBool "The updated model is the same as the original"    (model1' /= model1)

-- Update a model with the params from another and then chdck that
-- extraction returns the same params.
testExtractAfterUpdate ::  CekCostModel -> CekCostModel -> IO ()
testExtractAfterUpdate model1 model2 =
    do
      params <- extractParams model2
      updated <- applyParams model1 params
      params' <- extractParams updated
      params' @?= params

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
       , testGroup "overwriting works"
             [ testCase "defaultCekCostModel <- randomCekCostModel"  $ testOverwrite defaultCekCostModel randomCekCostModel
             , testCase "randomCekCostModel  <- defaultCekCostModel" $ testOverwrite randomCekCostModel  defaultCekCostModel
             ]
       , testGroup "superfluous entry in params is OK in self-update"
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
     ]
