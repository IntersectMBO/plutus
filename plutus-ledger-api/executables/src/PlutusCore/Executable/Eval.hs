{-# LANGUAGE TupleSections #-}

module PlutusCore.Executable.Eval where

import PlutusLedgerApi.Common
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek

evalCounting
  :: EvaluationContext
  -> MajorProtocolVersion
  -> UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
  -> ( Either
         (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
         (UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ())
     , ExBudget
     )
evalCounting evalCtx pv term =
  ( cekResultToEither (_cekReportResult report)
  , let CountingSt cost = _cekReportCost report in cost
  )
  where
    report = evaluateTerm counting pv Quiet evalCtx term
