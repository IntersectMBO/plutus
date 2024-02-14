-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}
{- | Conformance tests for the Agda implementation. -}
module Main (main) where

import Control.Monad.Trans.Except (ExceptT, runExceptT, withExceptT)

import MAlonzo.Code.Evaluator.Term (runUCountingAgda)
-- import MAlonzo.Code.Cost.Raw (HRawCostModel)

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

-- This type corresponds to Cost.Raw.RawCostModel from the Agda code.
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

-- Evaluate a UPLC program using the Agda CEK machine
agdaEvalUplcProg :: UplcEvaluator
agdaEvalUplcProg =
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
                       let tmNamed = runQuote $ runExceptT $
                                     withExceptT FreeVariableErrorE $ unDeBruijnTerm tmEvaluated
                           cost = ExBudget (ExCPU (fromInteger cpuCost)) (ExMemory (fromInteger memCost))
                       in
                         -- turn it back into a named term
                         case tmNamed of
                           Left _          -> Nothing
                           Right namedTerm -> Just (UPLC.Program () version namedTerm , cost)

{- | Any tests here currently fail, so they are marked as expected to fail.  Once
 a fix for a test is pushed, the test will succeed and should be removed from
 this list.  The entries of the list are paths from the root of
 plutus-conformance to the directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1"
-}
failingTests :: [FilePath]
failingTests = []

main :: IO ()
main = runUplcEvalTests agdaEvalUplcProg (\dir -> elem dir failingTests)
