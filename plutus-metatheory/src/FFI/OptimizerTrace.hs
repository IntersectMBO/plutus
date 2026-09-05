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
type Trace a = NonEmptySep (OptStage, Hints a) a

mkFfiOptimizerTrace
  :: OptimizerTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -> Trace FFI.UTerm
mkFfiOptimizerTrace (OptimizerTrace simplNonEmptySep) = go (reverse simplNonEmptySep)
  where
    -- Convert a term, which may be pre-term, post-term, or intermediate terms inside hints.
    convTerm :: UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a -> FFI.UTerm
    convTerm t = case UPLC.deBruijnTerm t of
      Right t' -> FFI.conv (void t')
      Left (err :: UPLC.FreeVariableError) -> error $ show err

    go
      :: [Optimization UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a]
      -> Trace FFI.UTerm
    go [] = error "Empty trace"
    go [Optimization before stage hints after] =
      Cons
        (convTerm before)
        (stage, convTerm <$> hints)
        (Singleton (convTerm after))
    -- ignore _after, it should be equal to subsequent before
    go (Optimization before stage hints _after : xs) =
      Cons (convTerm before) (stage, convTerm <$> hints) (go xs)

toEvalResult
  :: Maybe (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
  -> ExBudget
  -> EvalResult
toEvalResult res budget = case res of
  Just err -> EvalFailure (T.pack $ show err) cpu mem
  Nothing -> EvalSuccess cpu mem
  where
    cpu = fromSatInt $ coerce (exBudgetCPU budget)
    mem = fromSatInt $ coerce (exBudgetMemory budget)
