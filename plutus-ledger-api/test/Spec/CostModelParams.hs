-- editorconfig-checker-disable-file
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeApplications #-}
module Spec.CostModelParams where

-- import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModelParamsForTesting)

import PlutusLedgerApi.Common

import PlutusLedgerApi.Test.V3.EvaluationContext qualified as V3
import PlutusLedgerApi.V1 as V1
import PlutusLedgerApi.V2 as V2
import PlutusLedgerApi.V3 as V3

import Control.Monad.Except
import Control.Monad.Writer.Strict
import Data.Either
import Data.Foldable
import Data.List.Extra
import Data.Set as Set
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "costModelParams"
    [ testCase "length" $ do
            166 @=? length v1_ParamNames
            185 @=? length v2_ParamNames
            251 @=? length v3_ParamNames
    , testCase "tripping paramname" $ do
            for_ v1_ParamNames $ \ p ->
                assertBool "tripping v1 cm params failed" $ Just p == readParamName (showParamName p)
            for_ v2_ParamNames $ \ p ->
                assertBool "tripping v2 cm params failed" $ Just p == readParamName (showParamName p)
            for_ v3_ParamNames $ \ p ->
                assertBool "tripping v3 cm params failed" $ Just p == readParamName (showParamName p)
-- *** FIXME !!! *** : The introduction of the new bitwise builtins has messed
-- this up because defaultCostModelParamsForTesting is the cost model parameters
-- for model C, which now includes the new bitwise builtins.
--    , testCase "default values costmodelparamsfortesting" $ do
--            defaultCostModelParamsForTesting @=? Just (toCostModelParams V3.costModelParamsForTesting)
    , testCase "context length" $ do
            let costValuesForTesting = fmap snd V3.costModelParamsForTesting
            -- the `costModelParamsForTesting` reflects only the latest version (V3), so this should succeed because the lengths match
            assertBool "wrong number of arguments in V3.mkEvaluationContext" $ isRight $ runExcept $ runWriterT $ V3.mkEvaluationContext costValuesForTesting
            -- this one should succeed because we allow adding new builtins to an existing version, by appending new cost model parameters, for more info:
            -- See Note [Cost model parameters from the ledger's point of view]
            assertBool "larger number of params did not warn" $ hasWarnMoreParams (length v3_ParamNames) (1 + length v3_ParamNames) $
                runExcept $ runWriterT $ V3.mkEvaluationContext $ costValuesForTesting ++ [1] -- dummy param value appended
    , testCase "cost model parameters" $ do
         -- v1 is missing some cost model parameters because new builtins are added in v2
         assertBool "v1 params is not a proper subset of v2 params" $ v1_ParamNames `paramProperSubset` v2_ParamNames
         -- v1/v2 and v3 cost models are not comparable because we added new builtins in v3 but also
         -- removed some superseded cost model parameters.
         assertBool "v1 params and v3 params are comparable" $
           not (v1_ParamNames `paramSubset` v3_ParamNames)
           && not (v3_ParamNames `paramSubset` v1_ParamNames)
         assertBool "v2 params and v3 params are comparable" $
           not (v2_ParamNames `paramSubset` v3_ParamNames)
           && not (v3_ParamNames `paramSubset` v2_ParamNames)
    ]
  where
    hasWarnMoreParams :: Int -> Int -> Either a (b, [CostModelApplyWarn]) -> Bool
    hasWarnMoreParams testExpected testActual (Right (_,[CMTooManyParamsWarn{..}]))
        | testExpected==cmExpected && testActual==cmActual  = True
    hasWarnMoreParams _ _ _ = False

    paramProperSubset pA pB =
        Set.fromList (showParamName <$> pA) `Set.isProperSubsetOf` Set.fromList (showParamName <$> pB)

    paramSubset pA pB =
        Set.fromList (showParamName <$> pA) `Set.isSubsetOf` Set.fromList (showParamName <$> pB)

    v1_ParamNames = enumerate @V1.ParamName
    v2_ParamNames = enumerate @V2.ParamName
    v3_ParamNames = enumerate @V3.ParamName
