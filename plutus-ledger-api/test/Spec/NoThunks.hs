{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE TypeApplications #-}

module Spec.NoThunks (tests) where

import NoThunks.Class

import PlutusLedgerApi.V1 as V1
import PlutusLedgerApi.V2 as V2
import PlutusLedgerApi.V3 as V3

import PlutusCore.Evaluation.Machine.ExBudgetingDefaults as Plutu
import PlutusCore.Pretty

import Control.Monad.Except
import Control.Monad.Extra (whenJust)
import Control.Monad.Writer.Strict
import Data.List.Extra (enumerate)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
    testGroup
        "NoThunks"
        [ testCase "EvaluationContext V1" evaluationContextV1
        , testCase "EvaluationContext V2" evaluationContextV2
        , testCase "EvaluationContext V3" evaluationContextV3
        ]

costParams :: [Integer]
costParams = Map.elems (fromJust defaultCostModelParams)

evaluationContextV1 :: Assertion
evaluationContextV1 = do
    let v1CostParams = take (length $ enumerate @V1.ParamName) costParams
    !(evalCtx :: EvaluationContext) <-
        either (assertFailure . display) (pure . fst) $ runExcept $ runWriterT $
            V1.mkEvaluationContext v1CostParams
    failIfThunk =<< noThunks [] evalCtx

evaluationContextV2 :: Assertion
evaluationContextV2 = do
    let v2CostParams = take (length $ enumerate @V2.ParamName) costParams
    !(evalCtx :: EvaluationContext) <-
        either (assertFailure . display) (pure . fst) $ runExcept $ runWriterT $
            V2.mkEvaluationContext v2CostParams
    failIfThunk =<< noThunks [] evalCtx

evaluationContextV3 :: Assertion
evaluationContextV3 = do
    let v3CostParams = take (length $ enumerate @V3.ParamName) costParams
    !(evalCtx :: EvaluationContext) <-
        either (assertFailure . display) (pure . fst) $ runExcept $ runWriterT $
            V3.mkEvaluationContext v3CostParams
    failIfThunk =<< noThunks [] evalCtx

failIfThunk :: Show a => Maybe a -> IO ()
failIfThunk mbThunkInfo =
    whenJust mbThunkInfo $ \thunkInfo ->
        assertFailure $ "Unexpected thunk: " <> show thunkInfo
