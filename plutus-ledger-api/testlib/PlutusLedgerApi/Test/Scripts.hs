module PlutusLedgerApi.Test.Scripts
  ( uplcToScriptForEvaluation
  , compiledCodeToScriptForEvaluation

    -- * Example scripts
  , unitRedeemer
  , unitDatum
  ) where

import PlutusLedgerApi.Common
import PlutusLedgerApi.V1.Scripts
import PlutusTx.Code (CompiledCode)
import UntypedPlutusCore qualified as UPLC

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
