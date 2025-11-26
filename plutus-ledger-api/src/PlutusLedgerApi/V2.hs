-- editorconfig-checker-disable-file

-- | The interface to Plutus V2 for the ledger.
module PlutusLedgerApi.V2
  ( -- * Scripts
    Common.SerialisedScript
  , Common.ScriptForEvaluation
  , Common.serialisedScript
  , Common.deserialisedScript
  , Common.serialiseCompiledCode
  , Common.serialiseUPLC
  , deserialiseScript
  , Common.uncheckedDeserialiseUPLC

    -- * Running scripts
  , evaluateScriptRestricting
  , evaluateScriptCounting

    -- ** Protocol version
  , Common.MajorProtocolVersion (..)

    -- ** Verbose mode and log output
  , Common.VerboseMode (..)
  , Common.LogOutput

    -- * Costing-related types
  , Common.ExBudget (..)
  , V1.ExCPU (..)
  , V1.ExMemory (..)
  , V1.SatInt (unSatInt)
  , V1.fromSatInt

    -- ** Cost model
  , Common.EvaluationContext
  , EvaluationContext.mkEvaluationContext
  , ParamName.ParamName (..)
  , Common.CostModelApplyError (..)
  , Common.CostModelParams
  , Common.assertWellFormedCostModelParams

    -- * Context types
  , Contexts.ScriptContext (..)
  , Contexts.ScriptPurpose (..)

    -- ** Supporting types used in the context types

    -- *** Builtins
  , Common.BuiltinByteString
  , Common.toBuiltin
  , Common.fromBuiltin
  , Common.toOpaque
  , Common.fromOpaque

    -- *** Bytes
  , V1.LedgerBytes (..)
  , V1.fromBytes

    -- *** Certificates
  , V1.DCert (..)

    -- *** Credentials
  , V1.StakingCredential (..)
  , V1.Credential (..)

    -- *** Value
  , V1.Value (..)
  , V1.CurrencySymbol (..)
  , V1.TokenName (..)
  , V1.singleton
  , V1.unionWith
  , V1.adaSymbol
  , V1.adaToken
  , V1.Lovelace (..)

    -- *** Time
  , V1.POSIXTime (..)
  , V1.POSIXTimeRange

    -- *** Types for representing transactions
  , V1.Address (..)
  , V1.PubKeyHash (..)
  , Tx.TxId (..)
  , Contexts.TxInfo (..)
  , Tx.TxOut (..)
  , Tx.TxOutRef (..)
  , Contexts.TxInInfo (..)
  , Tx.OutputDatum (..)

    -- *** Intervals
  , V1.Interval (..)
  , V1.Extended (..)
  , V1.Closure
  , V1.UpperBound (..)
  , V1.LowerBound (..)
  , V1.always
  , V1.from
  , V1.to
  , V1.lowerBound
  , V1.upperBound
  , V1.strictLowerBound
  , V1.strictUpperBound

    -- *** Association maps
  , Map
  , unsafeFromList

    -- *** Newtypes and hash types
  , V1.ScriptHash (..)
  , V1.Redeemer (..)
  , V1.RedeemerHash (..)
  , V1.Datum (..)
  , V1.DatumHash (..)

    -- * Data
  , Common.Data (..)
  , Common.BuiltinData (..)
  , Common.ToData (..)
  , Common.FromData (..)
  , Common.UnsafeFromData (..)
  , Common.toData
  , Common.fromData
  , Common.unsafeFromData
  , Common.dataToBuiltinData
  , Common.builtinDataToData

    -- * Errors
  , Common.MonadError
  , Common.EvaluationError (..)
  , Common.ScriptDecodeError (..)
  ) where

import PlutusLedgerApi.Common qualified as Common
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2.Contexts qualified as Contexts
import PlutusLedgerApi.V2.EvaluationContext qualified as EvaluationContext
import PlutusLedgerApi.V2.ParamName qualified as ParamName
import PlutusLedgerApi.V2.Tx qualified as Tx

import PlutusTx.AssocMap (Map, unsafeFromList)

{-| An alias to the Plutus ledger language this module exposes at runtime.
 MAYBE: Use CPP '__FILE__' + some TH to automate this. -}
thisLedgerLanguage :: Common.PlutusLedgerLanguage
thisLedgerLanguage = Common.PlutusV2

{-| The deserialization from a serialised script into a `ScriptForEvaluation`,
ready to be evaluated on-chain.
Called inside phase-1 validation (i.e., deserialisation error is a phase-1 error). -}
deserialiseScript
  :: forall m
   . Common.MonadError Common.ScriptDecodeError m
  => Common.MajorProtocolVersion
  -- ^ which major protocol version the script was submitted in.
  -> Common.SerialisedScript
  -- ^ the script to deserialise.
  -> m Common.ScriptForEvaluation
deserialiseScript = Common.deserialiseScript thisLedgerLanguage

{-| Evaluates a script, returning the minimum budget that the script would need
to evaluate successfully. This will take as long as the script takes, if you need to
limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
also returns the used budget. -}
evaluateScriptCounting
  :: Common.MajorProtocolVersion
  -- ^ Which major protocol version to run the operation in
  -> Common.VerboseMode
  -- ^ Whether to produce log output
  -> Common.EvaluationContext
  -- ^ Includes the cost model to use for tallying up the execution costs
  -> Common.ScriptForEvaluation
  -- ^ The script to evaluate
  -> [Common.Data]
  -- ^ The arguments to the script
  -> (Common.LogOutput, Either Common.EvaluationError Common.ExBudget)
evaluateScriptCounting = Common.evaluateScriptCounting thisLedgerLanguage

{-| Evaluates a script, with a cost model and a budget that restricts how many
resources it can use according to the cost model. Also returns the budget that
was actually used.

Can be used to calculate budgets for scripts, but even in this case you must give
a limit to guard against scripts that run for a long time or loop. -}
evaluateScriptRestricting
  :: Common.MajorProtocolVersion
  -- ^ Which major protocol version to run the operation in
  -> Common.VerboseMode
  -- ^ Whether to produce log output
  -> Common.EvaluationContext
  -- ^ Includes the cost model to use for tallying up the execution costs
  -> Common.ExBudget
  -- ^ The resource budget which must not be exceeded during evaluation
  -> Common.ScriptForEvaluation
  -- ^ The script to evaluate
  -> [Common.Data]
  -- ^ The arguments to the script
  -> (Common.LogOutput, Either Common.EvaluationError Common.ExBudget)
evaluateScriptRestricting = Common.evaluateScriptRestricting thisLedgerLanguage
