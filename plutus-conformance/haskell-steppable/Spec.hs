{- | Conformance tests for the steppable (debuggable) Haskell implementation. -}

module Main (main) where

import PlutusConformance.Common
import PlutusCore.Evaluation.Machine.MachineParameters.Default
import PlutusPrelude
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.SteppableCek as SCek

failingEvaluationTests :: [FilePath]
failingEvaluationTests = []

failingBudgetTests :: [FilePath]
failingBudgetTests = []

-- | The `evaluator` for the steppable-version of the CEK machine.
evalSteppableUplcProg :: UplcEvaluator
evalSteppableUplcProg = UplcEvaluatorWithCosting $ \modelParams (UPLC.Program a v t) -> do
    params <- case mkMachineParametersFor [def] modelParams of
        Left _               -> Nothing
        Right machParamsList -> lookup def machParamsList
    -- runCek-like functions (e.g. evaluateCekNoEmit) are partial on term's with free variables,
    -- that is why we manually check first for any free vars
    case UPLC.deBruijnTerm t of
        Left (_ :: UPLC.FreeVariableError) -> Nothing
        Right _                            -> Just ()
    case SCek.runCekNoEmit params counting t of
        (Left _,_)                  -> Nothing
        (Right t', CountingSt cost) -> Just (UPLC.Program a v t', cost)

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests evalSteppableUplcProg
    (flip elem failingEvaluationTests) (flip elem failingBudgetTests)
