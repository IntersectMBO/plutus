{- | Conformance tests for the Haskell implementation. -}

module Main (main) where

import Control.Lens (traverseOf)
import PlutusConformance.Common
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (evaluateCekNoEmit)


-- | Our `evaluator` for the Haskell UPLC tests is the CEK machine.
evalUplcProg :: UplcEvaluator
evalUplcProg = traverseOf UPLC.progTerm eval
  where
    eval t = do
        -- The evaluator throws if the term has free variables
        case UPLC.deBruijnTerm t of
            Left (_ :: UPLC.FreeVariableError) -> Nothing
            Right _                            -> Just ()
        case evaluateCekNoEmit defaultCekParameters t of
            Left _     -> Nothing
            Right prog -> Just prog

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests evalUplcProg

