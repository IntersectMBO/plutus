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

-- import           Data.Aeson
import           Test.Tasty
import           Test.Tasty.HUnit

type CekCostModel = CostModel CekMachineCosts

-- Just for testing
randomCekCosts :: CekMachineCosts
randomCekCosts =
    CekMachineCosts { cekStartupCost = ExBudget 2342 234321
                    , cekVarCost     = ExBudget 12312 56545
                    , cekConstCost   = ExBudget 23490290838 2323423
                    , cekLamCost     = ExBudget 0 712127381
                    , cekDelayCost   = ExBudget 999 7777
                    , cekForceCost   = ExBudget 1028234 0
                    , cekApplyCost   = ExBudget 324628348 8273
                    , cekBuiltinCost = ExBudget 4 4
                    }

randomCekCostModel :: CekCostModel
randomCekCostModel = CostModel randomCekCosts defaultBuiltinCostModel

test_costModelInterface :: TestTree
test_costModelInterface =
    testGroup "cost model interface tests" [test_extract, test_apply]

test_extract :: TestTree
test_extract = testGroup "extractCostModelParams works"
               [ testCase "defaultCekCostModel" $ mkExtractionTest defaultCekCostModel
               , testCase "randomCekCostModel"    $ mkExtractionTest randomCekCostModel
               ]

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
      Nothing     ->  assertFailure "applyCostModelParams failed"
      Just model' -> pure model'

-- | Just check that extraction works.
mkExtractionTest :: CekCostModel -> IO ()
mkExtractionTest model = do
  _extracted <- extractParams model
--  putStrLn $ show _extracted
  pure ()

-- Update model1 with the parameters fom model2 and check that the extracted params from model1 match those from model2
mkUpdateTest :: CekCostModel -> CekCostModel -> IO ()
mkUpdateTest model1 model2 = do
    params1 <- extractParams model1
    updated <- applyParams model2 params1
    params2 <- extractParams updated
    params1 @?= params2

-- TODO: we could do with a test to check that if you extract the params from a
-- model M and then apply them to M, nothing changes.  We need an instance of Eq
-- for cost models for this, but that's tricky.  Can we fake one using toJSON
-- for example?

test_apply :: TestTree
test_apply = testGroup "applyCostModelParams works"
         [ testCase "defaultCekCostModel <- defaultCekCostModel" $ mkUpdateTest defaultCekCostModel defaultCekCostModel
         , testCase "defaultCekCostModel <- randomCekCostModel"  $ mkUpdateTest defaultCekCostModel randomCekCostModel
         , testCase "randomCekCostModel  <- randomCekCostModel"  $ mkUpdateTest randomCekCostModel  randomCekCostModel
         , testCase "randomCekCostModel  <- defaultCekCostModel" $ mkUpdateTest randomCekCostModel  defaultCekCostModel
         ]
