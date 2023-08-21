{- | Conformance tests for the steppable (debuggable) Haskell implementation. -}

module Main (main) where

import PlutusConformance.Common
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.SteppableCek qualified as SCek

import Control.Lens

failingTests :: [FilePath]
failingTests = []

-- | The `evaluator` for the steppable-version of the CEK machine.
evalSteppableUplcProg :: UplcEvaluator
evalSteppableUplcProg = traverseOf UPLC.progTerm $ \t -> do
    -- runCek-like functions (e.g. evaluateCekNoEmit) are partial on term's with free variables,
    -- that is why we manually check first for any free vars
    case UPLC.deBruijnTerm t of
        Left (_ :: UPLC.FreeVariableError) -> Nothing
        Right _                            -> Just ()
    case SCek.evaluateCekNoEmit defaultCekParameters t of
        Left _     -> Nothing
        Right prog -> Just prog

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests evalSteppableUplcProg (\dir -> elem dir failingTests)
