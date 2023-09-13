-- editorconfig-checker-disable-file
-- | The interface to Plutus V2 for the ledger.
module PlutusLedgerApi.V2 (
    -- * Scripts
      SerialisedScript
    , ScriptForEvaluation
    , serialisedScript
    , deserialisedScript
    , serialiseCompiledCode
    , serialiseUPLC
    , deserialiseScript
    , uncheckedDeserialiseUPLC
    -- * Running scripts
    , evaluateScriptRestricting
    , evaluateScriptCounting
    -- ** Protocol version
    , ProtocolVersion (..)
    -- ** Verbose mode and log output
    , VerboseMode (..)
    , LogOutput
    -- * Costing-related types
    , ExBudget (..)
    , ExCPU (..)
    , ExMemory (..)
    , SatInt
    -- ** Cost model
    , EvaluationContext
    , mkEvaluationContext
    , ParamName (..)
    , CostModelApplyError (..)
    , CostModelParams
    , assertWellFormedCostModelParams
    -- * Context types
    , ScriptContext(..)
    , ScriptPurpose(..)
    -- ** Supporting types used in the context types
    -- *** ByteStrings
    , BuiltinByteString
    , toBuiltin
    , fromBuiltin
    -- *** Bytes
    , LedgerBytes (..)
    , fromBytes
    -- *** Certificates
    , DCert(..)
    -- *** Credentials
    , StakingCredential(..)
    , Credential(..)
    -- *** Value
    , Value (..)
    , CurrencySymbol (..)
    , TokenName (..)
    , singleton
    , unionWith
    , adaSymbol
    , adaToken
    -- *** Time
    , POSIXTime (..)
    , POSIXTimeRange
    -- *** Types for representing transactions
    , Address (..)
    , PubKeyHash (..)
    , TxId (..)
    , TxInfo (..)
    , TxOut(..)
    , TxOutRef(..)
    , TxInInfo(..)
    , OutputDatum (..)
    -- *** Intervals
    , Interval (..)
    , Extended (..)
    , Closure
    , UpperBound (..)
    , LowerBound (..)
    , always
    , from
    , to
    , lowerBound
    , upperBound
    , strictLowerBound
    , strictUpperBound
    -- *** Association maps
    , Map
    , fromList
    -- *** Newtypes and hash types
    , ScriptHash (..)
    , Redeemer (..)
    , RedeemerHash (..)
    , Datum (..)
    , DatumHash (..)
    -- * Data
    , Data (..)
    , BuiltinData (..)
    , ToData (..)
    , FromData (..)
    , UnsafeFromData (..)
    , toData
    , fromData
    , dataToBuiltinData
    , builtinDataToData
    -- * Errors
    , EvaluationError (..)
    , ScriptDecodeError (..)
    ) where

import PlutusLedgerApi.Common as Common hiding (deserialiseScript, evaluateScriptCounting,
                                         evaluateScriptRestricting)
import PlutusLedgerApi.Common qualified as Common (deserialiseScript, evaluateScriptCounting,
                                                   evaluateScriptRestricting)
import PlutusLedgerApi.V1 hiding (ParamName, ScriptContext (..), TxInInfo (..), TxInfo (..),
                           TxOut (..), deserialiseScript, evaluateScriptCounting,
                           evaluateScriptRestricting, mkEvaluationContext)
import PlutusLedgerApi.V2.Contexts
import PlutusLedgerApi.V2.EvaluationContext
import PlutusLedgerApi.V2.ParamName
import PlutusLedgerApi.V2.Tx (OutputDatum (..))

import PlutusCore.Data qualified as PLC
import PlutusTx.AssocMap (Map, fromList)

import Control.Monad.Except (MonadError)

-- | An alias to the Plutus ledger language this module exposes at runtime.
--  MAYBE: Use CPP '__FILE__' + some TH to automate this.
thisLedgerLanguage :: PlutusLedgerLanguage
thisLedgerLanguage = PlutusV2

{- | The deserialization from a serialised script into a `ScriptForEvaluation`,
ready to be evaluated on-chain.
Called inside phase-1 validation (i.e., deserialisation error is a phase-1 error).
-}
deserialiseScript ::
  forall m.
  (MonadError ScriptDecodeError m) =>
  -- | which protocol version the script was submitted in.
  ProtocolVersion ->
  -- | the script to deserialise.
  SerialisedScript ->
  m ScriptForEvaluation
deserialiseScript = Common.deserialiseScript thisLedgerLanguage

-- | Evaluates a script, returning the minimum budget that the script would need
-- to evaluate successfully. This will take as long as the script takes, if you need to
-- limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
-- also returns the used budget.
evaluateScriptCounting
    :: ProtocolVersion   -- ^ Which protocol version to run the operation in
    -> VerboseMode       -- ^ Whether to produce log output
    -> EvaluationContext -- ^ Includes the cost model to use for tallying up the execution costs
    -> ScriptForEvaluation -- ^ The script to evaluate
    -> [PLC.Data]        -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting = Common.evaluateScriptCounting thisLedgerLanguage

-- | Evaluates a script, with a cost model and a budget that restricts how many
-- resources it can use according to the cost model. Also returns the budget that
-- was actually used.
--
-- Can be used to calculate budgets for scripts, but even in this case you must give
-- a limit to guard against scripts that run for a long time or loop.
evaluateScriptRestricting
    :: ProtocolVersion   -- ^ Which protocol version to run the operation in
    -> VerboseMode       -- ^ Whether to produce log output
    -> EvaluationContext -- ^ Includes the cost model to use for tallying up the execution costs
    -> ExBudget          -- ^ The resource budget which must not be exceeded during evaluation
    -> ScriptForEvaluation -- ^ The script to evaluate
    -> [PLC.Data]        -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting = Common.evaluateScriptRestricting thisLedgerLanguage
