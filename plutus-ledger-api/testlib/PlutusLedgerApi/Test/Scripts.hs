module PlutusLedgerApi.Test.Scripts
  ( uplcToScriptForEvaluation
  , compiledCodeToScriptForEvaluation
  , evaluateCekLikeInProd

    -- * Example scripts
  , unitRedeemer
  , unitDatum
  ) where

import PlutusCore qualified as PLC
import PlutusLedgerApi.Common
import PlutusLedgerApi.V1.Scripts
import PlutusTx.Code (CompiledCode)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

uplcToScriptForEvaluation
  :: PlutusLedgerLanguage
  -> MajorProtocolVersion
  -> UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
  -> Either ScriptDecodeError ScriptForEvaluation
uplcToScriptForEvaluation ll pv =
  deserialiseScript ll pv . serialiseUPLC

compiledCodeToScriptForEvaluation
  :: PlutusLedgerLanguage
  -> MajorProtocolVersion
  -> CompiledCode a
  -> Either ScriptDecodeError ScriptForEvaluation
compiledCodeToScriptForEvaluation ll pv =
  deserialiseScript ll pv . serialiseCompiledCode

-- | @()@ as a datum.
unitDatum :: Datum
unitDatum = Datum $ toBuiltinData ()

-- | @()@ as a redeemer.
unitRedeemer :: Redeemer
unitRedeemer = Redeemer $ toBuiltinData ()

{-| Evaluate a term as it would be evaluated using the on-chain evaluator.
Always use this for benchmarking UPLC scripts. -}
evaluateCekLikeInProd
  :: EvaluationContext
  -> UPLC.Term PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
  -> Either
       (Cek.CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
       (UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ())
evaluateCekLikeInProd evalCtx term =
  let
    pv = ledgerLanguageIntroducedIn PlutusV1
   in
    Cek.cekResultToEither . Cek._cekReportResult $
      evaluateTerm Cek.restrictingEnormous pv Quiet evalCtx term
