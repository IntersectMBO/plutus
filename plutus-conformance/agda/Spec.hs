-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}
{- | Conformance tests for the Agda implementation. -}
module Main (main) where

import Control.Monad.Trans.Except (ExceptT, runExceptT, withExceptT)

import MAlonzo.Code.Evaluator.Term (runUAgda, runUCountingAgda)

import PlutusConformance.Common (UplcEvaluator (..), runUplcEvalTests)
import PlutusCore (Error (..))
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Evaluation.Machine.CostModelInterface (CekMachineCosts, CostModelParams,
                                                         applyCostModelParams)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekCostModel)
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Evaluation.Machine.MachineParameters (CostModel (..))
import PlutusCore.Evaluation.Machine.SimpleBuiltinCostModel (BuiltinCostKeyMap, BuiltinCostMap,
                                                             toSimpleBuiltinCostModel)
import PlutusCore.Quote
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.DeBruijn

import Data.Aeson (Result (Error, Success), fromJSON, toJSON)

-- This type corresponds to Cost.Raw.RawCostModel in plutus-metaheory.
type RawCostModel = (CekMachineCosts, BuiltinCostMap)

{- Convert a set of `CostModelParams` into a `RawCostModel` suitable for use with
   the Agda CEK machine.  We convert the `CostModelParams` into a standard
   `CekCostModel`, then convert that to Aeson's `Value` type (its intermediate
   JSON representation), and then deserialise the `Value` to a `SimpleCostModel`
   which is packed together with the machine costs from the `CekCostModel`.
   This approach is similar to the one used by `applyCostModelParams` and is
   much simpler than trying to convert the parameters directly; also, it re-uses
   existing functions whose correctness we have a high degree on confidence in.
   There will be some extra overhead because of the conversion to `Value` and
   back (which will presumably happen for every test), but the tests still run
   very quickly.
-}
toRawCostModel :: CostModelParams -> RawCostModel
toRawCostModel params =
    let CostModel machineCosts builtinCosts =
            case applyCostModelParams defaultCekCostModel params of
              Left e  -> error $ show e
              Right r -> r

        costKeyMap =
            case fromJSON @BuiltinCostKeyMap $ toJSON builtinCosts of
               Error s   -> error s
               Success m -> m

    in (machineCosts, toSimpleBuiltinCostModel costKeyMap)

{- Note [Evaluation with and without costing]
   We provide two evaluators, one with costing and one without: normally the
   tests should be run with costing enabled.  It may occasionally be necessary
   to turn the costing off, for example if the Haskell costing implementation
   has changed and the Agda implementation has not yet caught up: to do this,
   change `WithCosting` to `WithoutCosting` in `main`.
-}
data CostOrNot = WithCosting | WithoutCosting

-- Evaluate a UPLC program using the Agda CEK machine
agdaEvalUplcProg :: CostOrNot -> UplcEvaluator
agdaEvalUplcProg WithCosting =
    UplcEvaluatorWithCosting $ \modelParams (UPLC.Program () version tmU) ->
        let
            -- turn the body of the program into an untyped de Bruijn term
            tmUDB :: ExceptT FreeVariableError Quote (UPLC.Term NamedDeBruijn DefaultUni DefaultFun ())
            tmUDB = deBruijnTerm tmU

        in case runQuote $ runExceptT $ withExceptT FreeVariableErrorE tmUDB of
             -- if there's an exception, evaluation failed, should return `Nothing`.
             Left _ -> Nothing
             -- evaluate the untyped term with the CEK evaluator
             Right tmUDBSuccess ->
                 case runUCountingAgda (toRawCostModel modelParams) tmUDBSuccess of
                   Left _ -> Nothing
                   Right (tmEvaluated,(cpuCost,memCost)) ->
                       -- turn it back into a named term
                       case runQuote $ runExceptT $
                            withExceptT FreeVariableErrorE $ unDeBruijnTerm tmEvaluated of
                         Left _          -> Nothing
                         Right namedTerm ->
                             let  cost = ExBudget (ExCPU (fromInteger cpuCost)) (ExMemory (fromInteger memCost))
                             in Just (UPLC.Program () version namedTerm , cost)

agdaEvalUplcProg WithoutCosting =
    UplcEvaluatorWithoutCosting $ \(UPLC.Program () version tmU) ->
        let tmUDB :: ExceptT FreeVariableError Quote (UPLC.Term NamedDeBruijn DefaultUni DefaultFun ())
            tmUDB = deBruijnTerm tmU
        in case runQuote $ runExceptT $ withExceptT FreeVariableErrorE tmUDB of
             Left _ -> Nothing
             Right tmUDBSuccess ->
                 case runUAgda tmUDBSuccess of
                   Left _ -> Nothing
                   Right tmEvaluated ->
                       case runQuote $ runExceptT $
                            withExceptT FreeVariableErrorE $ unDeBruijnTerm tmEvaluated of
                         Left _          -> Nothing
                         Right namedTerm -> Just $ UPLC.Program () version namedTerm

{- | Any tests here currently fail, so they are marked as expected to fail.  Once
 a fix for a test is pushed, the test will succeed and should be removed from
 this list.  The entries of the list are paths from the root of
 plutus-conformance to the directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1"
-}
failingTests :: [FilePath]
failingTests = []

-- Run the tests: see Note [Evaluation with and without costing] above.
main :: IO ()
main = runUplcEvalTests (agdaEvalUplcProg WithCosting) (\dir -> elem dir failingTests)
