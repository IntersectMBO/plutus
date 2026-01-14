{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeApplications #-}

module Spec.CostModelParams where

import           PlutusLedgerApi.Common                    (CostModelApplyWarn (CMTooManyParamsWarn, cmActual, cmExpected),
                                                            IsParamName (readParamName, showParamName))
import qualified PlutusLedgerApi.Test.V3.EvaluationContext as V3
import qualified PlutusLedgerApi.V1                        as V1
import qualified PlutusLedgerApi.V2                        as V2
import qualified PlutusLedgerApi.V3                        as V3

import           Control.Monad.Except                      (runExcept)
import           Control.Monad.Writer.Strict               (WriterT (runWriterT))
import           Data.Either                               (isRight)
import           Data.Foldable                             (for_)
import           Data.List.Extra                           (enumerate)
import           Data.Set                                  (isSubsetOf)
import qualified Data.Set                                  as Set
import qualified Data.Text                                 as Text
import           Test.Tasty.Extras                         (TestNested, embed,
                                                            nestedGoldenVsTextPredM,
                                                            testNestedNamed)
import           Test.Tasty.HUnit                          (assertBool,
                                                            testCase, (@=?))

tests :: TestNested
tests =
  testNestedNamed
    "CostModelParams"
    "costModelParams"
    [ embed $ testCase "length" do
        329 @=? length v1_ParamNames
        329 @=? length v2_ParamNames
        347 @=? length v3_ParamNames
    , embed $ testCase "tripping paramname" do
        for_ v1_ParamNames \p ->
          assertBool "tripping v1 cm params failed" $
            Just p == readParamName (showParamName p)
        for_ v2_ParamNames \p ->
          assertBool "tripping v2 cm params failed" $
            Just p == readParamName (showParamName p)
        for_ v3_ParamNames \p ->
          assertBool "tripping v3 cm params failed" $
            Just p == readParamName (showParamName p)
    , -- The introduction of the new bitwise builtins has
      -- messed this up because defaultCostModelParamsForTesting is the cost
      -- model parameters for model C,
      -- which now includes the new bitwise builtins.
      --  , embed $ testCase "default values costmodelparamsfortesting" do
      --    defaultCostModelParamsForTesting
      --      @=? Just (toCostModelParams V3.costModelParamsForTesting)
      embed $ testCase "context length" do
        let costValuesForTesting = fmap snd V3.costModelParamsForTesting
        -- the `costModelParamsForTesting` reflects only the latest
        -- version (V3), so this should succeed because the lengths match
        assertBool "wrong number of arguments in V3.mkEvaluationContext" $
          isRight $
            runExcept $
              runWriterT $
                V3.mkEvaluationContext costValuesForTesting
        -- this one should succeed because we allow adding new builtins to an
        -- existing version, by appending new cost model parameters,
        -- for more info:
        -- See Note [Cost model parameters from the ledger's point of view]
        assertBool "larger number of params did not warn"
          $ hasWarnMoreParams
            (length v3_ParamNames)
            (1 + length v3_ParamNames)
          $ runExcept
          $ runWriterT
          $ V3.mkEvaluationContext
          $ costValuesForTesting ++ [1] -- dummy param value appended
    , embed $ testCase "cost model parameters" do
        -- From PV11, the v1 and v2 parameter names are identical; before PV11
        -- the v1 parameter names were a subset of the v2 ones.
        assertBool "v1 params is not equal to v2 params" $
          v1_ParamNames `paramEqual` v2_ParamNames
        -- v1/v2 and v3 cost models are not comparable because we added
        -- new builtins in v3 but also removed some superseded cost model
        -- parameters.
        assertBool "v1 params and v3 params are comparable" $
          not (v1_ParamNames `paramSubset` v3_ParamNames)
            && not (v3_ParamNames `paramSubset` v1_ParamNames)
        assertBool "v2 params and v3 params are comparable" $
          not (v2_ParamNames `paramSubset` v3_ParamNames)
            && not (v3_ParamNames `paramSubset` v2_ParamNames)
    , -- Fail if new cost model parameters names aren't appended to the end
      nestedGoldenVsTextPredM
        "costModelParamNames"
        ".txt"
        do pure (Text.unlines (map showParamName v3_ParamNames))
        Text.isPrefixOf
    ]
  where
    hasWarnMoreParams :: Int -> Int -> Either a (b, [CostModelApplyWarn]) -> Bool
    hasWarnMoreParams
      testExpected
      testActual
      (Right (_, [CMTooManyParamsWarn {..}]))
        | testExpected == cmExpected && testActual == cmActual = True
    hasWarnMoreParams _ _ _ = False

    paramSubset pA pB =
      Set.fromList (showParamName <$> pA)
        `isSubsetOf` Set.fromList (showParamName <$> pB)

    paramEqual pA pB = paramSubset pA pB && paramSubset pB pA

    v1_ParamNames = enumerate @V1.ParamName
    v2_ParamNames = enumerate @V2.ParamName
    v3_ParamNames = enumerate @V3.ParamName
