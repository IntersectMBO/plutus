{-# OPTIONS_GHC -Wall #-}

module FFI.SimplifierTrace
  ( TraceElem
  , Trace
  , mkFfiSimplifierTrace
  , toEvalResult
  ) where

import FFI.CostInfo
import FFI.Untyped qualified as FFI
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Transform.Certify.Hints qualified as Certify
import UntypedPlutusCore.Transform.Simplifier

import Data.Coerce
import Data.Functor
import Data.SatInt
import Data.Text qualified as T

type TraceElem a = (SimplifierStage, (Certify.Hints, (a, a)))
type Trace a = [TraceElem a]

mkFfiSimplifierTrace
  :: SimplifierTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -> Trace FFI.UTerm
mkFfiSimplifierTrace (SimplifierTrace simplTrace) = reverse $ toFfiAst <$> simplTrace
  where
    toFfiAst (Simplification before stage hints after) =
      case (UPLC.deBruijnTerm before, UPLC.deBruijnTerm after) of
        (Right before', Right after') ->
          (stage, (hints, (FFI.conv (void before'), FFI.conv (void after'))))
        (Left (err :: UPLC.FreeVariableError), _) -> error $ show err
        (_, Left (err :: UPLC.FreeVariableError)) -> error $ show err

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
