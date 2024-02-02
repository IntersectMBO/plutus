-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}
{- | Conformance tests for the Agda implementation. -}
module Main (main) where

import Control.Monad.Trans.Except
import MAlonzo.Code.Evaluator.Term (runUCountingAgda)
import PlutusConformance.Common
import PlutusCore (Error (..))
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekMachineCosts)
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.SimpleBuiltinCostModel

import PlutusCore.Quote
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.DeBruijn

-- -- | Our `evaluator` for the Agda UPLC tests is the CEK machine without costs.
-- agdaEvalUplcProgNoCost :: UplcEvaluator
-- agdaEvalUplcProgNoCost = UplcEvaluatorWithoutCosting $ \(UPLC.Program () version tmU) ->
--     let
--         -- turn it into an untyped de Bruijn term
--         tmUDB :: ExceptT FreeVariableError Quote (UPLC.Term NamedDeBruijn DefaultUni DefaultFun ())
--         tmUDB = deBruijnTerm tmU
--     in
--     case runQuote $ runExceptT $ withExceptT FreeVariableErrorE tmUDB of
--         -- if there's an exception, evaluation failed, should return `Nothing`.
--         Left _ -> Nothing
--         -- evaluate the untyped term with CEK
--         Right tmUDBSuccess ->
--             case runUAgda tmUDBSuccess of
--                 Left _ -> Nothing
--                 Right tmEvaluated ->
--                     let tmNamed = runQuote $ runExceptT $
--                             withExceptT FreeVariableErrorE $ unDeBruijnTerm tmEvaluated
--                     in
--                     -- turn it back into a named term
--                     case tmNamed of
--                         Left _          -> Nothing
--                         Right namedTerm -> Just $ UPLC.Program () version namedTerm

-- | Our `evaluator` for the Agda UPLC tests is the CEK machine with costs.
agdaEvalUplcProg :: UplcEvaluator
agdaEvalUplcProg = UplcEvaluatorWithCosting $ \ modelParams (UPLC.Program () version tmU) ->
    let
        -- turn it into an untyped de Bruijn term
        tmUDB :: ExceptT FreeVariableError Quote (UPLC.Term NamedDeBruijn DefaultUni DefaultFun ())
        tmUDB = deBruijnTerm tmU

        {- TODO: In processModelParams construct the pair in the result from the argument.
          Here, we ignore the argument and just return a default set.
        -}
        processModelParams  :: CostModelParams -> (CekMachineCosts ,  BuiltinCostMap)
        processModelParams _ = (defaultCekMachineCosts , defaultSimpleBuiltinCostModel)

        defaultModelParams :: (CekMachineCosts ,  BuiltinCostMap)
        defaultModelParams = processModelParams modelParams
    in
    case runQuote $ runExceptT $ withExceptT FreeVariableErrorE tmUDB of
        -- if there's an exception, evaluation failed, should return `Nothing`.
        Left _ -> Nothing
        -- evaluate the untyped term with CEK
        Right tmUDBSuccess ->
            case runUCountingAgda defaultModelParams tmUDBSuccess of
                Left _ -> Nothing
                Right (tmEvaluated,(cpuCost,memCost)) ->
                    let tmNamed = runQuote $ runExceptT $
                            withExceptT FreeVariableErrorE $ unDeBruijnTerm tmEvaluated
                        cost = ExBudget (ExCPU (fromInteger cpuCost)) (ExMemory (fromInteger memCost))
                    in
                    -- turn it back into a named term
                    case tmNamed of
                        Left _          -> Nothing
                        Right namedTerm -> Just (UPLC.Program () version namedTerm , cost)

-- | These tests are currently failing so they are marked as expected to fail.
-- Once a fix for a test is pushed, the test will fail. Remove it from this list.
-- The entries of the list should be paths from the root of plutus-conformance
-- to the directory containing the test, eg
--   "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1"
failingTests :: [FilePath]
failingTests =
    [
    ]

main :: IO ()
main =
    -- UPLC evaluation tests
    runUplcEvalTests agdaEvalUplcProg (\dir -> elem dir failingTests)

