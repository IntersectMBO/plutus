-- editorconfig-checker-disable-file

-- | The interface to Plutus V3 for the ledger.
module PlutusLedgerApi.V3 (
    -- * Scripts
      SerialisedScript
    , serialiseCompiledCode
    , serialiseUPLC
    , uncheckedDeserialiseUPLC
    -- * Validating scripts
    , assertScriptWellFormed
    -- * Running scripts
    , evaluateScriptRestricting
    , evaluateScriptCounting
    -- ** CIP-1694
    , ColdCommitteeCredential (..)
    , HotCommitteeCredential (..)
    , DRepCredential (..)
    , DRep (..)
    , Delegatee (..)
    , TxCert (..)
    , Voter (..)
    , Vote (..)
    , GovernanceActionId (..)
    , Committee (..)
    , Constitution (..)
    , GovernanceAction (..)
    , ProposalProcedure (..)
    -- ** Protocol version
    , ProtocolVersion (..)
    -- ** Verbose mode and log output
    , VerboseMode (..)
    , LogOutput
    -- * Costing-related types
    , ExBudget (..)
    , V2.ExCPU (..)
    , V2.ExMemory (..)
    , V2.SatInt
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
    , V2.BuiltinByteString
    , V2.toBuiltin
    , V2.fromBuiltin
    -- *** Bytes
    , V2.LedgerBytes (..)
    , V2.fromBytes
    -- *** Credentials
    , V2.StakingCredential(..)
    , V2.Credential(..)
    -- *** Value
    , V2.Value (..)
    , V2.CurrencySymbol (..)
    , V2.TokenName (..)
    , V2.singleton
    , V2.unionWith
    , V2.adaSymbol
    , V2.adaToken
    -- *** Time
    , V2.POSIXTime (..)
    , V2.POSIXTimeRange
    -- *** Types for representing transactions
    , V2.Address (..)
    , V2.PubKeyHash (..)
    , V2.TxId (..)
    , TxInfo (..)
    , V2.TxOut(..)
    , V2.TxOutRef(..)
    , V2.TxInInfo(..)
    , V2.OutputDatum (..)
    -- *** Intervals
    , V2.Interval (..)
    , V2.Extended (..)
    , V2.Closure
    , V2.UpperBound (..)
    , V2.LowerBound (..)
    , V2.always
    , V2.from
    , V2.to
    , V2.lowerBound
    , V2.upperBound
    , V2.strictLowerBound
    , V2.strictUpperBound
    -- *** Association maps
    , V2.Map
    , V2.fromList
    -- *** Newtypes and hash types
    , V2.ScriptHash (..)
    , V2.Redeemer (..)
    , V2.RedeemerHash (..)
    , V2.Datum (..)
    , V2.DatumHash (..)
    -- * Data
    , V2.Data (..)
    , V2.BuiltinData (..)
    , V2.ToData (..)
    , V2.FromData (..)
    , V2.UnsafeFromData (..)
    , V2.toData
    , V2.fromData
    , V2.dataToBuiltinData
    , V2.builtinDataToData
    -- * Errors
    , V2.EvaluationError (..)
    , V2.ScriptDecodeError (..)
    ) where

import Control.Monad.Except (MonadError)

import PlutusLedgerApi.Common as Common hiding (ProtocolVersion (..), assertScriptWellFormed,
                                         evaluateScriptCounting, evaluateScriptRestricting)
import PlutusLedgerApi.Common qualified as Common (ProtocolVersion (..), assertScriptWellFormed,
                                                   evaluateScriptCounting,
                                                   evaluateScriptRestricting)
import PlutusLedgerApi.V2 qualified as V2 hiding (ScriptContext (..), ScriptPurpose (..),
                                           TxInfo (..))
import PlutusLedgerApi.V3.Contexts
import PlutusLedgerApi.V3.EvaluationContext
import PlutusLedgerApi.V3.ParamName

import PlutusCore.Data qualified as PLC

-- | An alias to the Plutus ledger language this module exposes at runtime.
--  MAYBE: Use CPP '__FILE__' + some TH to automate this.
thisLedgerLanguage :: PlutusLedgerLanguage
thisLedgerLanguage = PlutusV3

-- | Check if a 'Script' is "valid" according to a protocol version. At the moment this means "deserialises correctly", which in particular
-- implies that it is (almost certainly) an encoded script and the script does not mention any builtins unavailable in the given protocol version.
assertScriptWellFormed
    :: MonadError ScriptDecodeError m
    => Common.ProtocolVersion -- ^ which protocol version to run the operation in
    -> SerialisedScript -- ^ the script to check for well-formedness
    -> m ()
assertScriptWellFormed = Common.assertScriptWellFormed thisLedgerLanguage

-- | Evaluates a script, returning the minimum budget that the script would need
-- to evaluate successfully. This will take as long as the script takes, if you need to
-- limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
-- also returns the used budget.
evaluateScriptCounting
    :: Common.ProtocolVersion -- ^ Which protocol version to run the operation in
    -> VerboseMode            -- ^ Whether to produce log output
    -> EvaluationContext      -- ^ Includes the cost model to use for tallying up the execution costs
    -> SerialisedScript       -- ^ The script to evaluate
    -> [PLC.Data]             -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting = Common.evaluateScriptCounting thisLedgerLanguage

-- | Evaluates a script, with a cost model and a budget that restricts how many
-- resources it can use according to the cost model. Also returns the budget that
-- was actually used.
--
-- Can be used to calculate budgets for scripts, but even in this case you must give
-- a limit to guard against scripts that run for a long time or loop.
evaluateScriptRestricting
    :: Common.ProtocolVersion -- ^ Which protocol version to run the operation in
    -> VerboseMode            -- ^ Whether to produce log output
    -> EvaluationContext      -- ^ Includes the cost model to use for tallying up the execution costs
    -> ExBudget               -- ^ The resource budget which must not be exceeded during evaluation
    -> SerialisedScript       -- ^ The script to evaluate
    -> [PLC.Data]             -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting = Common.evaluateScriptRestricting thisLedgerLanguage
