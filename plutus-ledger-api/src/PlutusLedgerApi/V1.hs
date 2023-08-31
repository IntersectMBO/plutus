-- editorconfig-checker-disable-file
-- | The interface to Plutus V1 for the ledger.
module PlutusLedgerApi.V1 (
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
    -- *** Newtypes and hash types
    , ScriptHash (..)
    , Redeemer (..)
    , RedeemerHash (..)
    , Datum (..)
    , DatumHash (..)
    -- * Data
    , PLC.Data (..)
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

import Control.Monad.Except (MonadError)
import Data.SatInt
import PlutusCore.Data qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusLedgerApi.Common as Common hiding (assertScriptWellFormed, evaluateScriptCounting,
                                         evaluateScriptRestricting)
import PlutusLedgerApi.Common qualified as Common (assertScriptWellFormed, evaluateScriptCounting,
                                                   evaluateScriptRestricting)
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Bytes
import PlutusLedgerApi.V1.Contexts
import PlutusLedgerApi.V1.Credential
import PlutusLedgerApi.V1.Crypto
import PlutusLedgerApi.V1.DCert
import PlutusLedgerApi.V1.EvaluationContext
import PlutusLedgerApi.V1.Interval hiding (singleton)
import PlutusLedgerApi.V1.ParamName
import PlutusLedgerApi.V1.Scripts as Scripts
import PlutusLedgerApi.V1.Time
import PlutusLedgerApi.V1.Value
import PlutusTx (FromData (..), ToData (..), UnsafeFromData (..), fromData, toData)
import PlutusTx.Builtins.Internal (BuiltinData (..), builtinDataToData, dataToBuiltinData)
import PlutusTx.Prelude (BuiltinByteString, fromBuiltin, toBuiltin)

-- | An alias to the Plutus ledger language this module exposes at runtime.
--  MAYBE: Use CPP '__FILE__' + some TH to automate this.
thisLedgerLanguage :: PlutusLedgerLanguage
thisLedgerLanguage = PlutusV1

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

-- | Check if a 'Script' is "valid" according to a protocol version. At the moment this means "deserialises correctly", which in particular
-- implies that it is (almost certainly) an encoded script and the script does not mention any builtins unavailable in the given protocol version.
assertScriptWellFormed
    :: MonadError ScriptDecodeError m
    => ProtocolVersion -- ^ which protocol version to run the operation in
    -> SerialisedScript -- ^ the script to check for well-formedness
    -> m ()
assertScriptWellFormed = Common.assertScriptWellFormed thisLedgerLanguage

-- | Evaluates a script, returning the minimum budget that the script would need
-- to evaluate successfully. This will take as long as the script takes, if you need to
-- limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
-- also returns the used budget.
evaluateScriptCounting
    :: ProtocolVersion   -- ^ Which protocol version to run the operation in
    -> VerboseMode       -- ^ Whether to produce log output
    -> EvaluationContext -- ^ Includes the cost model to use for tallying up the execution costs
    -> SerialisedScript  -- ^ The script to evaluate
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
    -> SerialisedScript  -- ^ The script to evaluate
    -> [PLC.Data]        -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting = Common.evaluateScriptRestricting thisLedgerLanguage
