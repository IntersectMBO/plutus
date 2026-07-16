{-# LANGUAGE CPP #-}

-- | Conformance tests for the Haskell implementation.
module Main (main) where

import PlutusConformance.Common
  ( EvaluationResult (..)
  , UplcEvaluator (..)
  , runUplcEvalTests
  )
import PlutusCore.Evaluation.Machine.MachineParameters qualified as UPLC
import PlutusCore.Evaluation.Machine.MachineParameters.Default
import PlutusPrelude (def)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
  ( CountingSt (..)
  , counting
  , runCekNoEmit
  )

-- | Our `evaluator` for the Haskell UPLC tests is the CEK machine.
evalUplcProg :: UplcEvaluator
evalUplcProg = UplcEvaluatorWithCosting $ \modelParams (UPLC.Program a v t) ->
  case mkMachineVariantParametersFor [def] modelParams of
    Left _ -> BadMachineParameters
    Right machParamsList ->
      case lookup def machParamsList of
        Nothing -> BadMachineParameters
        Just p ->
          let params = UPLC.MachineParameters def p
           in -- runCek-like functions (e.g. evaluateCekNoEmit) are partial on term's with
              -- free variables, that is why we manually check first for any free vars
              case UPLC.deBruijnTerm t of
                Left (_ :: UPLC.FreeVariableError) -> DecodeError
                Right _ ->
                  case runCekNoEmit params counting t of
                    (Left _, _) -> EvalFailure
                    (Right prog, CountingSt cost) -> EvalSuccess (UPLC.Program a v prog, cost)

{-| A list of evaluation tests which are currently expected to fail.  Once a fix
 for a test is pushed, the test will succeed and should be removed from the
 list.  The entries of the list are paths from the root of plutus-conformance to
 the directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1" -}
failingEvaluationTests :: [FilePath]
failingEvaluationTests = []

{-| A list of budget tests which are currently expected to fail. Once a fix for
 a test is pushed, the test will succeed and should be removed from the list.
 The entries of the list are paths from the root of plutus-conformance to the
 directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1" -}
failingBudgetTests :: [FilePath]
failingBudgetTests = ["test-cases/uplc/evaluation/term/var"]

{- FIXME: The above test succeeds with the .uplc file but fails with the .flat
file.  The .budget.expected file contains "evaluation failure" which is correct
for the .uplc file but incorrect for the .flat file.  The problem is that the
file contains a free variable.  This causes a failure during flat decoding, but
not during parsing: in that case the error is only detected when the program is
de Bruijn-ified, and this is currently reported as an evaluation failure. -}

main :: IO ()
main =
  -- UPLC evaluation tests
  runUplcEvalTests
    evalUplcProg
    (flip elem failingEvaluationTests)
    (flip elem failingBudgetTests)
