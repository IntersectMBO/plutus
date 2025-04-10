{-# LANGUAGE CPP #-}

{- | Conformance tests for the Haskell implementation. -}

module Main (main) where

import PlutusConformance.Common (UplcEvaluator (..), runUplcEvalTests)
import PlutusCore.Evaluation.Machine.MachineParameters.Default
import PlutusPrelude (def)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (CountingSt (..), counting, runCekNoEmit)

-- | Our `evaluator` for the Haskell UPLC tests is the CEK machine.
evalUplcProg :: UplcEvaluator
evalUplcProg = UplcEvaluatorWithCosting $ \modelParams (UPLC.Program a v t) ->
    do
        params <- case mkMachineParametersFor [def] modelParams of
          Left _               -> Nothing
          Right machParamsList -> lookup def machParamsList
        -- runCek-like functions (e.g. evaluateCekNoEmit) are partial on term's with free variables,
        -- that is why we manually check first for any free vars
        case UPLC.deBruijnTerm t of
            Left (_ :: UPLC.FreeVariableError) -> Nothing
            Right _                            -> Just ()
        case runCekNoEmit params counting t of
            (Left _, _)                   -> Nothing
            (Right prog, CountingSt cost) -> Just (UPLC.Program a v prog, cost)

{- | A list of evaluation tests which are currently expected to fail.  Once a fix
 for a test is pushed, the test will succeed and should be removed from the
 list.  The entries of the list are paths from the root of plutus-conformance to
 the directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1"
-}
failingEvaluationTests :: [FilePath]
#if MIN_VERSION_base(4,15,0)
failingEvaluationTests = []
#else
-- dropList not supported for GHC 8.10
failingEvaluationTests = [
    "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-01"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-02"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-03"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-04"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-05"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-06"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-07"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-08"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-09"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-10"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-11"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-12"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-13"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-14"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-15"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-16"
  ]
#endif

{- | A list of budget tests which are currently expected to fail.  Once a fix for
 a test is pushed, the test will succeed and should be removed from the list.
 The entries of the list are paths from the root of plutus-conformance to the
 directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1"
-}
failingBudgetTests :: [FilePath]
#if MIN_VERSION_base(4,15,0)
failingBudgetTests = []
#else
-- dropList not supported for GHC 8.10
failingBudgetTests = [
    "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-01"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-02"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-03"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-04"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-05"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-06"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-07"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-08"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-09"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-10"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-11"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-12"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-13"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-14"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-15"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-16"
  ]
#endif

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests evalUplcProg (flip elem failingEvaluationTests) (flip elem failingBudgetTests)
