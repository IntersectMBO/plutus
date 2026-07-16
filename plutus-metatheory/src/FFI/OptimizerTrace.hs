{-# OPTIONS_GHC -Wall #-}

module FFI.OptimizerTrace
  ( Trace
  , mkFfiOptimizerTrace
  , toEvalResult
  ) where

import FFI.CostInfo
import FFI.Untyped qualified as FFI
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Transform.Certify.Hints (Hints)
import UntypedPlutusCore.Transform.Optimizer
import Prelude hiding (head)

import Data.Coerce
import Data.Functor
import Data.List.NonEmptySep
import Data.SatInt
import Data.Text qualified as T

-- A certifier trace is a non-empty list of asts of type `a`, separated by the
-- optimizer pass that ran and the hints that were emitted
type Trace a = NonEmptySep (OptStage, Hints) a

mkFfiOptimizerTrace
  :: OptimizerTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun UPLC.DefaultBuiltinPattern a
  -> Trace FFI.UTerm
mkFfiOptimizerTrace (OptimizerTrace simplNonEmptySep) = go (reverse simplNonEmptySep)
  where
    go
      :: [ Optimization
             UPLC.Name
             UPLC.DefaultUni
             UPLC.DefaultFun
             UPLC.DefaultBuiltinPattern
             a
         ]
      -> Trace FFI.UTerm
    go [] = error "Empty trace"
    go [Optimization before stage hints after] =
      case (UPLC.deBruijnTerm before, UPLC.deBruijnTerm after) of
        (Right before', Right after') ->
          Cons
            (FFI.conv (void before'))
            (stage, hints)
            (Singleton (FFI.conv (void after')))
        (Left (err :: UPLC.FreeVariableError), _) -> error $ show err
        (_, Left (err :: UPLC.FreeVariableError)) -> error $ show err
    -- ignore _after, it should be equal to subsequent before
    go (Optimization before stage hints _after : xs) =
      case UPLC.deBruijnTerm before of
        Right before' ->
          Cons (FFI.conv (void before')) (stage, hints) (go xs)
        Left (err :: UPLC.FreeVariableError) -> error $ show err

toEvalResult
  :: Maybe
       (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun UPLC.DefaultBuiltinPattern)
  -> ExBudget
  -> EvalResult
toEvalResult res budget = case res of
  Just err -> EvalFailure (T.pack $ show err) cpu mem
  Nothing -> EvalSuccess cpu mem
  where
    cpu = fromSatInt $ coerce (exBudgetCPU budget)
    mem = fromSatInt $ coerce (exBudgetMemory budget)
