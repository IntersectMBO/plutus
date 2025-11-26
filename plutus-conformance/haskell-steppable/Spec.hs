{-# LANGUAGE CPP #-}

-- | Conformance tests for the steppable (debuggable) Haskell implementation.
module Main (main) where

import PlutusConformance.Common
import PlutusCore.Evaluation.Machine.MachineParameters qualified as UPLC
import PlutusCore.Evaluation.Machine.MachineParameters.Default
import PlutusPrelude
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.SteppableCek as SCek

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
evalSteppableUplcProg = UplcEvaluatorWithCosting $
  \modelParams (UPLC.Program a v t) -> do
    params <- case mkMachineVariantParametersFor [def] modelParams of
      Left _ -> Nothing
      Right machParamsList -> UPLC.MachineParameters def <$> lookup def machParamsList
    -- runCek-like functions (e.g. evaluateCekNoEmit) are partial on term's with
    -- free variables, that is why we manually check first for any free vars
    case UPLC.deBruijnTerm t of
      Left (_ :: UPLC.FreeVariableError) -> Nothing
      Right _ -> Just ()
    case SCek.runCekNoEmit params counting t of
      (Left _, _) -> Nothing
      (Right t', CountingSt cost) -> Just (UPLC.Program a v t', cost)

main :: IO ()
main =
  -- UPLC evaluation tests
  runUplcEvalTests
    evalSteppableUplcProg
    (flip elem failingEvaluationTests)
    (flip elem failingBudgetTests)
