{-# LANGUAGE CPP #-}

-- | Conformance tests for the steppable (debuggable) Haskell implementation.
module Main (main) where

import PlutusConformance.CekEvaluator (mkCekEvaluator)
import PlutusConformance.Common (UplcEvaluator, runUplcEvalTests)
import UntypedPlutusCore.Evaluation.Machine.SteppableCek (runCekNoEmit)

{-| A list of evaluation tests which are currently expected to fail.  Once a fix
 for a test is pushed, the test will succeed and should be removed from the
 list.  The entries of the list are paths from the root of plutus-conformance to
 the directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1" -}
failingEvaluationTests :: [FilePath]
failingEvaluationTests = []

{-| A list of budget tests which are currently expected to fail.  Once a fix for
 a test is pushed, the test will succeed and should be removed from the list.
 The entries of the list are paths from the root of plutus-conformance to the
 directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1" -}
failingBudgetTests :: [FilePath]
failingBudgetTests = []

-- | The `evaluator` for the steppable-version of the CEK machine.
evalSteppableUplcProg :: UplcEvaluator
evalSteppableUplcProg = mkCekEvaluator runCekNoEmit

main :: IO ()
main =
  -- UPLC evaluation tests
  runUplcEvalTests
    evalSteppableUplcProg
    (flip elem failingEvaluationTests)
    (flip elem failingBudgetTests)
