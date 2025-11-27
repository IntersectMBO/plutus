-- editorconfig-checker-disable-file

-- | The interface to Plutus V1 for the ledger.
module PlutusLedgerApi.V1
  ( -- * Scripts
    Scripts.ScriptHash (..)
  , Scripts.Redeemer (..)
  , Scripts.RedeemerHash (..)
  , Scripts.Datum (..)
  , Scripts.DatumHash (..)
  , Scripts.Context (..)
  , Scripts.ScriptError (..)

    -- ** Script (de)serialization
  , SerialisedScript.SerialisedScript
  , SerialisedScript.ScriptForEvaluation
  , SerialisedScript.ScriptDecodeError (..)
  , SerialisedScript.ScriptNamedDeBruijn (..)
  , SerialisedScript.serialisedScript
  , SerialisedScript.deserialisedScript
  , SerialisedScript.serialiseCompiledCode
  , SerialisedScript.serialiseUPLC
  , deserialiseScript
  , SerialisedScript.uncheckedDeserialiseUPLC

    -- ** Running scripts
  , evaluateScriptRestricting
  , evaluateScriptCounting

    -- * Protocol version
  , Common.MajorProtocolVersion (..)

    -- * Costing-related types
  , Common.ExBudget (..)
  , Common.ExCPU (..)
  , Common.ExMemory (..)
  , Common.SatInt (unSatInt)
  , Common.fromSatInt
  , ParamName.ParamName (..)
  , ParamName.tagWithParamNames

    -- * Evaluation
  , Eval.EvaluationError (..)
  , Eval.EvaluationContext
  , Eval.AsScriptDecodeError (..)
  , Eval.LogOutput
  , Eval.VerboseMode (..)
  , Eval.evaluateTerm
  , Eval.mkDynEvaluationContext
  , Eval.toMachineParameters
  , Eval.mkTermToEvaluate
  , Eval.assertWellFormedCostModelParams

    -- ** Evaluation context
  , EvaluationContext.mkEvaluationContext
  , EvaluationContext.CostModelParams
  , EvaluationContext.CostModelApplyError (..)

    -- * Script Context
  , Contexts.TxInfo (..)
  , Contexts.ScriptContext (..)
  , Contexts.ScriptPurpose (..)
  , Contexts.TxId (..)
  , Contexts.TxOut (..)
  , Contexts.TxOutRef (..)
  , Contexts.TxInInfo (..)
  , Contexts.findOwnInput
  , Contexts.findDatum
  , Contexts.findDatumHash
  , Contexts.findTxInByTxOutRef
  , Contexts.findContinuingOutputs
  , Contexts.getContinuingOutputs
  , Contexts.pubKeyOutputsAt
  , Contexts.valuePaidTo
  , Contexts.spendsOutput
  , Contexts.txSignedBy
  , Contexts.valueSpent
  , Contexts.valueProduced
  , Contexts.ownCurrencySymbol

    -- * Builtins
  , Common.BuiltinByteString
  , Common.toBuiltin
  , Common.fromBuiltin
  , Common.toOpaque
  , Common.fromOpaque

    -- * Bytes
  , Bytes.LedgerBytes (..)
  , Bytes.LedgerBytesError (..)
  , Bytes.fromBytes
  , Bytes.fromHex
  , Bytes.bytes
  , Bytes.encodeByteString

    -- * Certificates
  , DCert.DCert (..)

    -- * Credentials
  , Credential.StakingCredential (..)
  , Credential.Credential (..)

    -- * Value
  , Value.Value (..)
  , Value.Lovelace (..)
  , Value.currencySymbolValueOf
  , Value.flattenValue
  , Value.isZero
  , Value.lovelaceValue
  , Value.lovelaceValueOf
  , Value.scale
  , Value.singleton
  , Value.split
  , Value.unionWith
  , Value.valueOf

    -- ** Currency symbols
  , Value.CurrencySymbol (..)
  , Value.currencySymbol
  , Value.adaSymbol
  , Value.symbols

    -- ** Token names
  , Value.TokenName (..)
  , Value.tokenName
  , Value.adaToken

    -- ** Asset classes
  , Value.AssetClass (..)
  , Value.assetClass
  , Value.assetClassValue
  , Value.assetClassValueOf

    -- * Addresses
  , Address.Address (..)
  , Address.pubKeyHashAddress
  , Address.toPubKeyHash
  , Address.toScriptHash
  , Address.scriptHashAddress
  , Address.stakingCredential

    -- * Crypto
  , Crypto.PubKeyHash (..)

    -- * Time
  , Time.POSIXTime (..)
  , Time.POSIXTimeRange
  , Time.DiffMilliSeconds (..)
  , Time.fromMilliSeconds

    -- ** Intervals
  , Interval.Interval (..)
  , Interval.Extended (..)
  , Interval.Closure
  , Interval.UpperBound (..)
  , Interval.LowerBound (..)
  , Interval.never
  , Interval.always
  , Interval.from
  , Interval.to
  , Interval.lowerBound
  , Interval.upperBound
  , Interval.strictLowerBound
  , Interval.strictUpperBound
  , Interval.member
  , Interval.interval
  , Interval.hull
  , Interval.intersection
  , Interval.overlaps
  , Interval.contains
  , Interval.isEmpty
  , Interval.before
  , Interval.after

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
  ) where

import PlutusLedgerApi.Common qualified as Common
import PlutusLedgerApi.Common.Eval qualified as Eval
import PlutusLedgerApi.Common.SerialisedScript qualified as SerialisedScript
import PlutusLedgerApi.V1.Address qualified as Address
import PlutusLedgerApi.V1.Bytes qualified as Bytes
import PlutusLedgerApi.V1.Contexts qualified as Contexts
import PlutusLedgerApi.V1.Credential qualified as Credential
import PlutusLedgerApi.V1.Crypto qualified as Crypto
import PlutusLedgerApi.V1.DCert qualified as DCert
import PlutusLedgerApi.V1.EvaluationContext qualified as EvaluationContext
import PlutusLedgerApi.V1.Interval qualified as Interval
import PlutusLedgerApi.V1.ParamName qualified as ParamName
import PlutusLedgerApi.V1.Scripts as Scripts
import PlutusLedgerApi.V1.Time qualified as Time
import PlutusLedgerApi.V1.Value qualified as Value

{-| An alias to the Plutus ledger language this module exposes at runtime.
 MAYBE: Use CPP '__FILE__' + some TH to automate this. -}
thisLedgerLanguage :: Common.PlutusLedgerLanguage
thisLedgerLanguage = Common.PlutusV1

{- Note [Abstract types in the ledger API]
We need to support old versions of the ledger API as we update the code that it depends on. You
might think that we should therefore make the types that we expose abstract, and only expose
specific functions for constructing and working with them. However the situation is slightly
different for us.

Normally, when you are in this situation, you want to retain the same *interface* as the old version,
but with the new types and functions underneath. Abstraction lets you do this easily. But we actually
want to keep the old *implementation*, because things really have to work the same, bug-for-bug. And
the types have to translate into Plutus Core in exactly the same way, and so on.

So we're going to end up with multiple versions of the types and functions that we expose here, even
internally. That means we don't lose anything by exposing all the details: we're never going to remove
anything, we're just going to create new versions.
-}

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
deserialiseScript = SerialisedScript.deserialiseScript thisLedgerLanguage

{-| Evaluates a script, returning the minimum budget that the script would need
to evaluate successfully. This will take as long as the script takes, if you need to
limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
also returns the used budget. -}
evaluateScriptCounting
  :: Common.MajorProtocolVersion
  -- ^ Which major protocol version to run the operation in
  -> Common.VerboseMode
  -- ^ Whether to produce log output
  -> EvaluationContext.EvaluationContext
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
  -> EvaluationContext.EvaluationContext
  -- ^ Includes the cost model to use for tallying up the execution costs
  -> Common.ExBudget
  -- ^ The resource budget which must not be exceeded during evaluation
  -> Common.ScriptForEvaluation
  -- ^ The script to evaluate
  -> [Common.Data]
  -- ^ The arguments to the script
  -> (Common.LogOutput, Either Common.EvaluationError Common.ExBudget)
evaluateScriptRestricting = Common.evaluateScriptRestricting thisLedgerLanguage
