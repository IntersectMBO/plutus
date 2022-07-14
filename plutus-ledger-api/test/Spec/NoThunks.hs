{-# LANGUAGE BangPatterns #-}

module Spec.NoThunks (tests) where

import Plutus.ApiCommon (mkEvaluationContext)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModelParams)
import PlutusCore.Pretty

import Control.Monad.Extra (whenJust)
import Data.Maybe (fromJust)
import NoThunks.Class
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
    testGroup
        "NoThunks"
        [ testCase "EvaluationContext V1" evaluationContextV1
        ]

evaluationContextV1 :: Assertion
evaluationContextV1 = do
    !evalCtx <-
        either (assertFailure . display) pure $
            mkEvaluationContext (fromJust defaultCostModelParams)
    failIfThunk =<< noThunks [] evalCtx

failIfThunk :: Show a => Maybe a -> IO ()
failIfThunk mbThunkInfo =
    whenJust mbThunkInfo $ \thunkInfo ->
        assertFailure $ "Unexpected thunk: " <> show thunkInfo
