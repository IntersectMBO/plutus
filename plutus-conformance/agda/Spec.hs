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
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekCostModelForTesting)
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
            case applyCostModelParams defaultCekCostModelForTesting params of
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

{- | A list of evaluation tests which are currently expected to fail.  Once a fix
 for a test is pushed, the test will succeed and should be removed from the
 list.  The entries of the list are paths from the root of plutus-conformance to
 the directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1"
-}
failingEvaluationTests :: [FilePath]
failingEvaluationTests = []

{- | A list of budget tests which are currently expected to fail.  Once a fix for
 a test is pushed, the test will succeed and should be removed from the list.
 The entries of the list are paths from the root of plutus-conformance to the
 directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1"
-}
failingBudgetTests :: [FilePath]
failingBudgetTests =
  -- These currently fail because the Agda code doesn't know about alternative
  -- size measures used by `replicateByte` and `writeBits`: see
  -- https://github.com/IntersectMBO/plutus/pull/6368.  Some of the budget tests
  -- do pass, either because evaluation fails or because two different size
  -- measures happen to be the same for small inputs.
  [ "test-cases/uplc/evaluation/builtin/semantics/replicateByte/case-7"
  , "test-cases/uplc/evaluation/builtin/semantics/replicateByte/case-9"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-11"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-12"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-13"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-14"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-15"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-16"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-17"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-18"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-19"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-20"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-21"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-22"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-23"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-24"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-25"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-26"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-27"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-28"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-29"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-30"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-31"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-32"
  , "test-cases/uplc/evaluation/builtin/semantics/writeBits/case-33"
  ]

-- Run the tests: see Note [Evaluation with and without costing] above.
main :: IO ()
main = runUplcEvalTests (agdaEvalUplcProg WithCosting)
       (flip elem failingEvaluationTests) (flip elem failingBudgetTests)
