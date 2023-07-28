-- editorconfig-checker-disable-file
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeApplications #-}
module Spec.CostModelParams where

import PlutusLedgerApi.Common
import PlutusLedgerApi.V1 as V1
import PlutusLedgerApi.V2 as V2
import PlutusLedgerApi.V3 as V3

import PlutusLedgerApi.Test.EvaluationContext

import Control.Monad.Except
import Control.Monad.Writer.Strict
import Data.Either
import Data.List.Extra
import Data.Map as Map
import Data.Set as Set
import Data.Text qualified as Text
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "costModelParams"
    [ testCase "length" $ do
            166 @=? length (enumerate @V1.ParamName)
            175 @=? length (enumerate @V2.ParamName)
            223 @=? length (enumerate @V3.ParamName)
            -- FIXME: the following three tests are misleading; better to directly test that
            -- their `showParamName` implemementation is injective
            166 @=? length v1CostModelParamNames
            175 @=? length v2CostModelParamNames
            223 @=? length v3CostModelParamNames
    , testCase "context length" $ do
            let costValuesForTesting = Map.elems costModelParamsForTesting
            -- the `costModelParamsForTesting` reflects only the latest version V3, so this should succeed because the lengths match
            assertBool "wrong number of arguments in V3.mkContext" $ isRight $ runExcept $ runWriterT $ V3.mkEvaluationContext costValuesForTesting
            -- this one should succeed because we pass more params
            assertBool "larger number of params did not warn" $ hasWarnMoreParams (length v3CostModelParamNames) (length v3CostModelParamNames+1) $
                runExcept $ runWriterT $ V3.mkEvaluationContext $ costValuesForTesting ++ [1] -- dummy param value appended
    , testCase "cost model parameters" $ do
         -- v1 is missing some cost model parameters because new builtins are added in v2
         assertBool "v1 params is proper subset of v2 params" $ Set.fromList v1CostModelParamNames `Set.isProperSubsetOf` Set.fromList v2CostModelParamNames
         -- v2 is missing some cost model parameters because new builtins and term constructors are added in v3
         assertBool "v2 params is proper subset of v3 params" $ Set.fromList v2CostModelParamNames `Set.isProperSubsetOf` Set.fromList v3CostModelParamNames
    ]
  where
    hasWarnMoreParams :: Int -> Int -> Either a (b, [CostModelApplyWarn]) -> Bool
    hasWarnMoreParams testExpected testActual (Right (_,[CMTooManyParamsWarn{..}]))
        | testExpected==cmTooManyExpected && testActual==cmTooManyActual  = True
    hasWarnMoreParams _ _ _ = False

v1CostModelParamNames :: [Text.Text]
v1CostModelParamNames = Text.pack . showParamName <$> enumerate @V1.ParamName

v2CostModelParamNames :: [Text.Text]
v2CostModelParamNames = Text.pack . showParamName <$> enumerate @V2.ParamName

v3CostModelParamNames :: [Text.Text]
v3CostModelParamNames = Text.pack . showParamName <$> enumerate @V3.ParamName

