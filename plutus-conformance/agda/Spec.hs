-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}

-- | Conformance tests for the Agda implementation.
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

{- Convert a set of `CostModelParams` into a `RawCostModel` suitable for use
   with the Agda CEK machine.  We convert the `CostModelParams` into a standard
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
      tmUDB
        :: ExceptT
             FreeVariableError
             Quote
             (UPLC.Term NamedDeBruijn DefaultUni DefaultFun ())
      tmUDB = deBruijnTerm tmU
     in
      case runQuote $ runExceptT $ withExceptT FreeVariableErrorE tmUDB of
        -- if there's an exception, evaluation failed, should return `Nothing`.
        Left _ -> Nothing
        -- evaluate the untyped term with the CEK evaluator
        Right tmUDBSuccess ->
          case runUCountingAgda (toRawCostModel modelParams) tmUDBSuccess of
            Left _ -> Nothing
            Right (tmEvaluated, (cpuCost, memCost)) ->
              -- turn it back into a named term
              case runQuote $
                runExceptT $
                  withExceptT FreeVariableErrorE $
                    unDeBruijnTerm tmEvaluated of
                Left _ -> Nothing
                Right namedTerm ->
                  let cost =
                        ExBudget
                          (ExCPU (fromInteger cpuCost))
                          (ExMemory (fromInteger memCost))
                   in Just (UPLC.Program () version namedTerm, cost)
agdaEvalUplcProg WithoutCosting =
  UplcEvaluatorWithoutCosting $ \(UPLC.Program () version tmU) ->
    let tmUDB
          :: ExceptT
               FreeVariableError
               Quote
               (UPLC.Term NamedDeBruijn DefaultUni DefaultFun ())
        tmUDB = deBruijnTerm tmU
     in case runQuote $ runExceptT $ withExceptT FreeVariableErrorE tmUDB of
          Left _ -> Nothing
          Right tmUDBSuccess ->
            case runUAgda tmUDBSuccess of
              Left _ -> Nothing
              Right tmEvaluated ->
                case runQuote $
                  runExceptT $
                    withExceptT FreeVariableErrorE $
                      unDeBruijnTerm tmEvaluated of
                  Left _          -> Nothing
                  Right namedTerm -> Just $ UPLC.Program () version namedTerm

{-| A list of evaluation tests which are currently expected to fail.  Once a fix
 for a test is pushed, the test will succeed and should be removed from the
 list.  The entries of the list are paths from the root of plutus-conformance to
 the directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1"
-}
failingEvaluationTests :: [FilePath]
failingEvaluationTests =
  [ -- These "constant casing" tests fail because Agda metatheory does not yet
    -- implement casing on constant values.
    -- TODO: remove these tests once casing on constant is added to Agda metatheory.
    "test-cases/uplc/evaluation/term/constant-case/bool/bool-01"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-02"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-03"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-04"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-05"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-06"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-07"
  , "test-cases/uplc/evaluation/term/constant-case/integer/integer-01"
  , "test-cases/uplc/evaluation/term/constant-case/integer/integer-02"
  , "test-cases/uplc/evaluation/term/constant-case/integer/integer-03"
  , "test-cases/uplc/evaluation/term/constant-case/integer/integer-04"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-01"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-02"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-03"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-04"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-05"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-06"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-07"
  , "test-cases/uplc/evaluation/term/constant-case/pair/pair-01"
  , "test-cases/uplc/evaluation/term/constant-case/pair/pair-02"
  , "test-cases/uplc/evaluation/term/constant-case/pair/pair-03"
  , "test-cases/uplc/evaluation/term/constant-case/pair/pair-04"
  , "test-cases/uplc/evaluation/term/constant-case/pair/pair-05"
  , "test-cases/uplc/evaluation/term/constant-case/unit/unit-01"
  , "test-cases/uplc/evaluation/term/constant-case/unit/unit-02"
  , "test-cases/uplc/evaluation/term/constant-case/unit/unit-03"

  -- The following are failing because the metatheory needs to be updated with
  -- Value built-in functions
  , "test-cases/uplc/evaluation/builtin/constant/value/duplicate-keys"
  , "test-cases/uplc/evaluation/builtin/constant/value/empty-tokens"
  , "test-cases/uplc/evaluation/builtin/constant/value/empty"
  , "test-cases/uplc/evaluation/builtin/constant/value/ill-formed"
  , "test-cases/uplc/evaluation/builtin/constant/value/multi"
  , "test-cases/uplc/evaluation/builtin/constant/value/unordered"
  , "test-cases/uplc/evaluation/builtin/constant/value/zero-asset"
  , "test-cases/uplc/evaluation/builtin/constant/value/max-key-length-1"
  , "test-cases/uplc/evaluation/builtin/constant/value/max-key-length-2"
  , "test-cases/uplc/evaluation/builtin/constant/value/overflow"
  , "test-cases/uplc/evaluation/builtin/constant/value/no-overflow"
  , "test-cases/uplc/evaluation/builtin/constant/value/underflow"
  , "test-cases/uplc/evaluation/builtin/constant/value/no-underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/multi-ccy-empty"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/multi-ccy-nonempty"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/multi-token"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/negative-empty"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/positive-empty"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/positive-nonempty"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/zero-positive"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/no-overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/no-underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/long-key-zero"
  , "test-cases/uplc/evaluation/builtin/semantics/lookupCoin/absent"
  , "test-cases/uplc/evaluation/builtin/semantics/lookupCoin/present"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/cancel-01"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/cancel-02"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/combine"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/unitl"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/unitr"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/no-overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/no-underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/ccy-missing"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/pos-empty"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/neg-empty"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/multi-insufficient"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/multi-sufficient"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/neg-neg-eq"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/neg-neg-gt"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/neg-neg-lt"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/neg-pos"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/pos-neg"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/reflexive"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/token-missing"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/by-zero"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/by-pos"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/by-neg"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/no-overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/no-underflow"
  ]

{-| A list of budget tests which are currently expected to fail.  Once a fix for
 a test is pushed, the test will succeed and should be removed from the list.
 The entries of the list are paths from the root of plutus-conformance to the
 directory containing the test, eg
 "test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger1"
-}
failingBudgetTests :: [FilePath]
failingBudgetTests =
  -- These currently fail because the Agda code doesn't know about the
  -- IntegerCostedLiterally size measure used by `replicateByte` and `dropList`.
  [ "test-cases/uplc/evaluation/builtin/semantics/replicateByte/case-07"
  , "test-cases/uplc/evaluation/builtin/semantics/replicateByte/case-09"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-01"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-02"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-03"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-04"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-05"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-06"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-07"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-08"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-09"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-10"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-11"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-12"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-13"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-14"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-15"
  , "test-cases/uplc/evaluation/builtin/semantics/dropList/dropList-16"
  -- These "constant casing" tests fail because Agda metatheory does not yet
  -- implement casing on constant values.
  -- TODO: remove these tests once casing on constant is added to Agda metatheory.
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-01"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-02"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-03"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-04"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-05"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-06"
  , "test-cases/uplc/evaluation/term/constant-case/bool/bool-07"
  , "test-cases/uplc/evaluation/term/constant-case/integer/integer-01"
  , "test-cases/uplc/evaluation/term/constant-case/integer/integer-02"
  , "test-cases/uplc/evaluation/term/constant-case/integer/integer-03"
  , "test-cases/uplc/evaluation/term/constant-case/integer/integer-04"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-01"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-02"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-03"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-04"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-05"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-06"
  , "test-cases/uplc/evaluation/term/constant-case/list/list-07"
  , "test-cases/uplc/evaluation/term/constant-case/pair/pair-01"
  , "test-cases/uplc/evaluation/term/constant-case/pair/pair-02"
  , "test-cases/uplc/evaluation/term/constant-case/pair/pair-03"
  , "test-cases/uplc/evaluation/term/constant-case/pair/pair-04"
  , "test-cases/uplc/evaluation/term/constant-case/pair/pair-05"
  , "test-cases/uplc/evaluation/term/constant-case/unit/unit-01"
  , "test-cases/uplc/evaluation/term/constant-case/unit/unit-02"
  , "test-cases/uplc/evaluation/term/constant-case/unit/unit-03"
  -- The following are failing because the metatheory needs to be updated with
  -- Value built-in functions
  , "test-cases/uplc/evaluation/builtin/constant/value/duplicate-keys"
  , "test-cases/uplc/evaluation/builtin/constant/value/empty-tokens"
  , "test-cases/uplc/evaluation/builtin/constant/value/empty"
  , "test-cases/uplc/evaluation/builtin/constant/value/ill-formed"
  , "test-cases/uplc/evaluation/builtin/constant/value/multi"
  , "test-cases/uplc/evaluation/builtin/constant/value/unordered"
  , "test-cases/uplc/evaluation/builtin/constant/value/zero-asset"
  , "test-cases/uplc/evaluation/builtin/constant/value/max-key-length-1"
  , "test-cases/uplc/evaluation/builtin/constant/value/max-key-length-2"
  , "test-cases/uplc/evaluation/builtin/constant/value/overflow"
  , "test-cases/uplc/evaluation/builtin/constant/value/no-overflow"
  , "test-cases/uplc/evaluation/builtin/constant/value/underflow"
  , "test-cases/uplc/evaluation/builtin/constant/value/no-underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/multi-ccy-empty"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/multi-ccy-nonempty"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/multi-token"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/negative-empty"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/positive-empty"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/positive-nonempty"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/zero-positive"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/no-overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/no-underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/insertCoin/long-key-zero"
  , "test-cases/uplc/evaluation/builtin/semantics/lookupCoin/absent"
  , "test-cases/uplc/evaluation/builtin/semantics/lookupCoin/present"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/cancel-01"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/cancel-02"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/combine"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/unitl"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/unitr"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/no-overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/unionValue/no-underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/ccy-missing"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/pos-empty"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/neg-empty"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/multi-insufficient"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/multi-sufficient"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/neg-neg-eq"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/neg-neg-gt"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/neg-neg-lt"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/neg-pos"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/pos-neg"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/reflexive"
  , "test-cases/uplc/evaluation/builtin/semantics/valueContains/token-missing"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/by-zero"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/by-pos"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/by-neg"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/underflow"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/no-overflow"
  , "test-cases/uplc/evaluation/builtin/semantics/scaleValue/no-underflow"
  ]

-- Run the tests: see Note [Evaluation with and without costing] above.
main :: IO ()
main =
  runUplcEvalTests
    (agdaEvalUplcProg WithCosting)
    (flip elem failingEvaluationTests)
    (flip elem failingBudgetTests)
