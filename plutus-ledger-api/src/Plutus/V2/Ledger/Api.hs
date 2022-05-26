{-# LANGUAGE DerivingStrategies #-}
{- |
The interface to Plutus V2 for the ledger.
-}
module Plutus.V2.Ledger.Api (
    -- * Scripts
    SerializedScript
    , Script
    , fromCompiledCode
    -- * Validating scripts
    , isScriptWellFormed
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
    , CostModelApplyError (..)
    , CostModelParams
    , assertWellFormedCostModelParams
    , costModelParamNames
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
    -- *** Newtypes for script/datum types and hash types
    , Validator (..)
    , mkValidatorScript
    , unValidatorScript
    , ValidatorHash (..)
    , MintingPolicy (..)
    , mkMintingPolicyScript
    , unMintingPolicyScript
    , MintingPolicyHash (..)
    , StakeValidator (..)
    , mkStakeValidatorScript
    , unStakeValidatorScript
    , StakeValidatorHash (..)
    , Redeemer (..)
    , RedeemerHash (..)
    , Datum (..)
    , DatumHash (..)
    , ScriptHash (..)
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
) where

import Plutus.ApiCommon as Common hiding (evaluateScriptCounting, evaluateScriptRestricting, isScriptWellFormed)
import Plutus.ApiCommon qualified as Common (evaluateScriptCounting, evaluateScriptRestricting, isScriptWellFormed)
import Plutus.V1.Ledger.Api hiding (ScriptContext (..), TxInInfo (..), TxInfo (..), TxOut (..), costModelParamNames,
                             evaluateScriptCounting, evaluateScriptRestricting, isScriptWellFormed, mkEvaluationContext)
import Plutus.V1.Ledger.Scripts (ScriptHash (..))
import Plutus.V2.Ledger.Contexts
import Plutus.V2.Ledger.EvaluationContext
import Plutus.V2.Ledger.Tx (OutputDatum (..))


import PlutusCore.Data qualified as PLC
import PlutusTx.AssocMap (Map, fromList)

-- | Check if a 'Script' is "valid" according to a protocol version. At the moment this means "deserialises correctly", which in particular
-- implies that it is (almost certainly) an encoded script and the script does not mention any builtins unavailable in the given protocol version.
isScriptWellFormed :: ProtocolVersion -> SerializedScript -> Bool
isScriptWellFormed = Common.isScriptWellFormed PlutusV2

-- | Evaluates a script, returning the minimum budget that the script would need
-- to evaluate successfully. This will take as long as the script takes, if you need to
-- limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
-- also returns the used budget.
evaluateScriptCounting
    :: ProtocolVersion
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> SerializedScript          -- ^ The script to evaluate
    -> [PLC.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting = Common.evaluateScriptCounting PlutusV2

-- | Evaluates a script, with a cost model and a budget that restricts how many
-- resources it can use according to the cost model. Also returns the budget that
-- was actually used.
--
-- Can be used to calculate budgets for scripts, but even in this case you must give
-- a limit to guard against scripts that run for a long time or loop.
evaluateScriptRestricting
    :: ProtocolVersion
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> ExBudget        -- ^ The resource budget which must not be exceeded during evaluation
    -> SerializedScript          -- ^ The script to evaluate
    -> [PLC.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting = Common.evaluateScriptRestricting PlutusV2
