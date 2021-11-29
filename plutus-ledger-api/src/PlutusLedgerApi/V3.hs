-- editorconfig-checker-disable-file

-- | The interface to Plutus V3 for the ledger.
module PlutusLedgerApi.V3 (
    -- * Scripts
      SerialisedScript
    , serialiseCompiledCode
    , serialiseUPLC
    , deserialiseUPLC
    -- ** Plutus Core terms themselves, only to be
    -- used for the script context
    , PlutusCoreTerm
    , scriptContextToTerm
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

import Control.Monad.Except (MonadError)

import PlutusLedgerApi.Common as Common hiding (assertScriptWellFormed, evaluateScriptCounting,
                                         evaluateScriptRestricting)
import PlutusLedgerApi.Common qualified as Common (assertScriptWellFormed, evaluateScriptCounting,
                                                   evaluateScriptRestricting)
import PlutusLedgerApi.V1 hiding (ParamName, ScriptContext (..), TxInInfo (..), TxInfo (..), TxOut (..),
                           assertScriptWellFormed, evaluateScriptCounting, evaluateScriptRestricting,
                           mkEvaluationContext)
import PlutusLedgerApi.V2.Contexts
import PlutusLedgerApi.V2.Tx (OutputDatum (..))
import PlutusLedgerApi.V3.EvaluationContext
import PlutusLedgerApi.V3.ParamName

import PlutusCore.Data qualified as PLC
import PlutusCore.MkPlc qualified as PLC
import PlutusTx.AssocMap (Map, fromList)
import PlutusTx.LiftU

scriptContextToTerm :: ScriptContext -> PlutusCoreTerm
scriptContextToTerm = liftU

-- | An alias to the language version this module exposes at runtime.
--  MAYBE: Use CPP '__FILE__' + some TH to automate this.
thisPlutusVersion :: LedgerPlutusVersion
thisPlutusVersion = PlutusV3

-- | Check if a 'Script' is "valid" according to a protocol version. At the moment this means "deserialises correctly", which in particular
-- implies that it is (almost certainly) an encoded script and the script does not mention any builtins unavailable in the given protocol version.
assertScriptWellFormed :: MonadError ScriptDecodeError m
                       => ProtocolVersion -- ^ which protocol version to run the operation in
                       -> SerialisedScript -- ^ the script to check for well-formedness
                       -> m ()
assertScriptWellFormed = Common.assertScriptWellFormed thisPlutusVersion

-- | Evaluates a script, returning the minimum budget that the script would need
-- to evaluate successfully. This will take as long as the script takes, if you need to
-- limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
-- also returns the used budget.
evaluateScriptCounting
    :: ProtocolVersion -- ^ which protocol version to run the operation in
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ Includes the cost model to use for tallying up the execution costs
    -> SerialisedScript          -- ^ The script to evaluate
    -> [PLC.Data]          -- ^ The 'Data' arguments to the script
    -> PlutusCoreTerm -- ^ A final argument as a fully-constructed Plutus Core term
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting pv verbose ec script args finalArg =
  let dataArgs = fmap (PLC.mkConstant ()) args
      allArgs = dataArgs ++ [finalArg]
  in Common.evaluateScriptCounting thisPlutusVersion pv verbose ec script allArgs

-- | Evaluates a script, with a cost model and a budget that restricts how many
-- resources it can use according to the cost model. Also returns the budget that
-- was actually used.
--
-- Can be used to calculate budgets for scripts, but even in this case you must give
-- a limit to guard against scripts that run for a long time or loop.
evaluateScriptRestricting
    :: ProtocolVersion -- ^ which protocol version to run the operation in
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ Includes the cost model to use for tallying up the execution costs
    -> ExBudget        -- ^ The resource budget which must not be exceeded during evaluation
    -> SerialisedScript          -- ^ The script to evaluate
    -> [PLC.Data]          -- ^ The 'Data' arguments to the script
    -> PlutusCoreTerm -- ^ A final argument as a fully-constructed Plutus Core term
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting pv verbose ec budget script args finalArg =
  let dataArgs = fmap (PLC.mkConstant ()) args
      allArgs = dataArgs ++ [finalArg]
  in Common.evaluateScriptRestricting thisPlutusVersion pv verbose ec budget script allArgs

{- Note [Passing the ScriptContext as a term]
In the PlutusV3 ledger language version we pass the ScriptContext as a term using the support for
sums and products in Plutus Core V2.

This requires the ledger to transform a ScriptContext into a Plutus Core term. We use
the LiftU typeclass for this. This transformation needs to be clear (and well-specified), but it
*doesn't* need to be stable - this isn't an external format that we're exposing.
-}
