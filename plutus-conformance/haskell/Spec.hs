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

failingTests :: [FilePath]
failingTests = []

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests evalUplcProg (\dir -> elem dir failingTests)
