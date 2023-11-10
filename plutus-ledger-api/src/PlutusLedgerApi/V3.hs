-- editorconfig-checker-disable-file

-- | The interface to Plutus V3 for the ledger.
module PlutusLedgerApi.V3 (
  -- * Scripts
  SerialisedScript,
  ScriptForEvaluation,
  serialisedScript,
  deserialisedScript,
  serialiseCompiledCode,
  serialiseUPLC,
  deserialiseScript,
  uncheckedDeserialiseUPLC,

  -- * Running scripts
  evaluateScriptRestricting,
  evaluateScriptCounting,

  -- ** CIP-1694
  ColdCommitteeCredential (..),
  HotCommitteeCredential (..),
  DRepCredential (..),
  DRep (..),
  Delegatee (..),
  TxCert (..),
  Voter (..),
  Vote (..),
  GovernanceActionId (..),
  Committee (..),
  Constitution (..),
  GovernanceAction (..),
  ChangedParameters (..),
  ProposalProcedure (..),

  -- ** Protocol version
  MajorProtocolVersion (..),

  -- ** Verbose mode and log output
  VerboseMode (..),
  LogOutput,

  -- * Costing-related types
  ExBudget (..),
  V2.ExCPU (..),
  V2.ExMemory (..),
  V2.SatInt,

  -- ** Cost model
  EvaluationContext,
  mkEvaluationContext,
  ParamName (..),
  CostModelApplyError (..),
  CostModelParams,
  assertWellFormedCostModelParams,

  -- * Context types
  ScriptContext (..),
  ScriptPurpose (..),

  -- ** Supporting types used in the context types

  -- *** ByteStrings
  V2.BuiltinByteString,
  V2.toBuiltin,
  V2.fromBuiltin,

  -- *** Bytes
  V2.LedgerBytes (..),
  V2.fromBytes,

  -- *** Credentials
  V2.StakingCredential (..),
  V2.Credential (..),

  -- *** Value
  V2.Value (..),
  V2.CurrencySymbol (..),
  V2.TokenName (..),
  V2.singleton,
  V2.unionWith,
  V2.adaSymbol,
  V2.adaToken,

  -- *** Time
  V2.POSIXTime (..),
  V2.POSIXTimeRange,

  -- *** Types for representing transactions
  V2.Address (..),
  V2.PubKeyHash (..),
  V2.TxId (..),
  TxInfo (..),
  V2.TxOut (..),
  V2.TxOutRef (..),
  V2.TxInInfo (..),
  V2.OutputDatum (..),

  -- *** Intervals
  V2.Interval (..),
  V2.Extended (..),
  V2.Closure,
  V2.UpperBound (..),
  V2.LowerBound (..),
  V2.always,
  V2.from,
  V2.to,
  V2.lowerBound,
  V2.upperBound,
  V2.strictLowerBound,
  V2.strictUpperBound,

  -- *** Association maps
  V2.Map,
  V2.fromList,

  -- *** Newtypes and hash types
  V2.ScriptHash (..),
  V2.Redeemer (..),
  V2.RedeemerHash (..),
  V2.Datum (..),
  V2.DatumHash (..),

  -- * Data
  V2.Data (..),
  V2.BuiltinData (..),
  V2.ToData (..),
  V2.FromData (..),
  V2.UnsafeFromData (..),
  V2.toData,
  V2.fromData,
  V2.dataToBuiltinData,
  V2.builtinDataToData,

  -- * Errors
  V2.EvaluationError (..),
  V2.ScriptDecodeError (..),
) where

import PlutusLedgerApi.Common as Common hiding (deserialiseScript, evaluateScriptCounting,
                                         evaluateScriptRestricting)
import PlutusLedgerApi.Common qualified as Common (deserialiseScript, evaluateScriptCounting,
                                                   evaluateScriptRestricting)
import PlutusLedgerApi.V2 qualified as V2 hiding (ScriptContext (..), ScriptPurpose (..),
                                           TxInfo (..))
import PlutusLedgerApi.V3.Contexts
import PlutusLedgerApi.V3.EvaluationContext
import PlutusLedgerApi.V3.ParamName

import PlutusCore.Data qualified as PLC

import Control.Monad.Except (MonadError)

{- | An alias to the Plutus ledger language this module exposes at runtime.
 MAYBE: Use CPP '__FILE__' + some TH to automate this.
-}
thisLedgerLanguage :: PlutusLedgerLanguage
thisLedgerLanguage = PlutusV3

{- | The deserialization from a serialised script into a `ScriptForEvaluation`,
ready to be evaluated on-chain.
Called inside phase-1 validation (i.e., deserialisation error is a phase-1 error).
-}
deserialiseScript ::
  forall m.
  (MonadError ScriptDecodeError m) =>
  -- | which major protocol version the script was submitted in.
  MajorProtocolVersion ->
  -- | the script to deserialise.
  SerialisedScript ->
  m ScriptForEvaluation
deserialiseScript = Common.deserialiseScript thisLedgerLanguage

{- | Evaluates a script, returning the minimum budget that the script would need
to evaluate successfully. This will take as long as the script takes, if you need to
limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
also returns the used budget.
-}
evaluateScriptCounting ::
  -- | Which protocol version to run the operation in
  MajorProtocolVersion ->
  -- | Whether to produce log output
  VerboseMode ->
  -- | Includes the cost model to use for tallying up the execution costs
  EvaluationContext ->
  -- | The script to evaluate
  ScriptForEvaluation ->
  -- | The arguments to the script
  [PLC.Data] ->
  (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting = Common.evaluateScriptCounting thisLedgerLanguage

{- | Evaluates a script, with a cost model and a budget that restricts how many
resources it can use according to the cost model. Also returns the budget that
was actually used.

Can be used to calculate budgets for scripts, but even in this case you must give
a limit to guard against scripts that run for a long time or loop.
-}
evaluateScriptRestricting ::
  -- | Which protocol version to run the operation in
  MajorProtocolVersion ->
  -- | Whether to produce log output
  VerboseMode ->
  -- | Includes the cost model to use for tallying up the execution costs
  EvaluationContext ->
  -- | The resource budget which must not be exceeded during evaluation
  ExBudget ->
  -- | The script to evaluate
  ScriptForEvaluation ->
  -- | The arguments to the script
  [PLC.Data] ->
  (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting = Common.evaluateScriptRestricting thisLedgerLanguage
