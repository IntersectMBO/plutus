{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}

{- |
The interface to Plutus V1 for the ledger.
-}
module Plutus.V1.Ledger.Api (
    -- * Scripts
    SerializedScript
    , Script
    , fromCompiledCode
    -- * Validating scripts
    , isScriptWellFormed
    -- * Running scripts
    , evaluateScriptRestricting
    , evaluateScriptCounting
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
    , CostModelParams
    , isCostModelParamsWellFormed
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
) where

import Codec.Serialise qualified as CBOR
import Control.Monad.Except
import Control.Monad.Writer
import Data.Bifunctor
import Data.ByteString.Lazy (fromStrict)
import Data.ByteString.Short
import Data.Either
import Data.SatInt
import Data.Text (Text)
import Data.Tuple
import Plutus.V1.Ledger.Address
import Plutus.V1.Ledger.Bytes
import Plutus.V1.Ledger.Contexts
import Plutus.V1.Ledger.Credential
import Plutus.V1.Ledger.Crypto
import Plutus.V1.Ledger.DCert
import Plutus.V1.Ledger.EvaluationContext
import Plutus.V1.Ledger.Interval hiding (singleton)
import Plutus.V1.Ledger.Scripts as Scripts
import Plutus.V1.Ledger.Time
import Plutus.V1.Ledger.Value
import PlutusCore as PLC
import PlutusCore.Data qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.MkPlc qualified as PLC
import PlutusCore.Pretty
import PlutusPrelude (through)
import PlutusTx (FromData (..), ToData (..), UnsafeFromData (..), fromData, toData)
import PlutusTx.Builtins.Internal (BuiltinData (..), builtinDataToData, dataToBuiltinData)
import PlutusTx.Prelude (BuiltinByteString, fromBuiltin, toBuiltin)
import Prettyprinter
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Check.Scope qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

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

-- | Check if a 'Script' is "valid". At the moment this just means "deserialises correctly", which in particular
-- implies that it is (almost certainly) an encoded script and cannot be interpreted as some other kind of encoded data.
isScriptWellFormed :: SerializedScript -> Bool
isScriptWellFormed = isRight . CBOR.deserialiseOrFail @Script . fromStrict . fromShort

data VerboseMode = Verbose | Quiet
    deriving (Eq)

type LogOutput = [Text]

-- | Scripts to the ledger are serialised bytestrings.
type SerializedScript = ShortByteString

-- | Errors that can be thrown when evaluating a Plutus script.
data EvaluationError =
    CekError (UPLC.CekEvaluationException PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun) -- ^ An error from the evaluator itself
    | DeBruijnError PLC.FreeVariableError -- ^ An error in the pre-evaluation step of converting from de-Bruijn indices
    | CodecError CBOR.DeserialiseFailure -- ^ A serialisation error
    | IncompatibleVersionError (PLC.Version ()) -- ^ An error indicating a version tag that we don't support
    -- TODO: make this error more informative when we have more information about what went wrong
    | CostModelParameterMismatch -- ^ An error indicating that the cost model parameters didn't match what we expected
    deriving stock (Show, Eq)

instance Pretty EvaluationError where
    pretty (CekError e)      = prettyClassicDef e
    pretty (DeBruijnError e) = pretty e
    pretty (CodecError e) = viaShow e
    pretty (IncompatibleVersionError actual) = "This version of the Plutus Core interface does not support the version indicated by the AST:" <+> pretty actual
    pretty CostModelParameterMismatch = "Cost model parameters were not as we expected"

{-| A variant of `Script` with a specialized `Serialise` instance
that decodes the names directly into `NamedDeBruijn`s rather than `DeBruijn`s.
This is needed because the CEK machine expects `NameDeBruijn`s, but there are obviously no names in the serialized form of a `Script`.
Rather than traversing the term and inserting fake names after deserializing, this lets us do at the same time as deserializing.
-}
newtype ScriptForExecution = ScriptForExecution (UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ())
  -- Identical to the deriving instance for `Script`, *except* that it specifies `FakeNamedDeBruijn`
  deriving CBOR.Serialise via (SerialiseViaFlat (UPLC.WithSizeLimits 64 (UPLC.Program UPLC.FakeNamedDeBruijn PLC.DefaultUni PLC.DefaultFun ())))

-- | Shared helper for the evaluation functions, deserializes the 'SerializedScript' , applies it to its arguments, puts fakenamedebruijns, and scope-checks it.
mkTermToEvaluate :: (MonadError EvaluationError m) => SerializedScript -> [PLC.Data] -> m (UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ())
mkTermToEvaluate bs args = do
    -- It decodes the program through the optimized ScriptForExecution. See `ScriptForExecution`.
    ScriptForExecution (UPLC.Program _ v t) <- liftEither $ first CodecError $ CBOR.deserialiseOrFail $ fromStrict $ fromShort bs
    unless (v == PLC.defaultVersion ()) $ throwError $ IncompatibleVersionError v
    let termArgs = fmap (PLC.mkConstant ()) args
        appliedT = PLC.mkIterApp () t termArgs
    -- make sure that term is closed, i.e. well-scoped
    through (liftEither . first DeBruijnError . UPLC.checkScope) appliedT

-- | Evaluates a script, with a cost model and a budget that restricts how many
-- resources it can use according to the cost model. Also returns the budget that
-- was actually used.
--
-- Can be used to calculate budgets for scripts, but even in this case you must give
-- a limit to guard against scripts that run for a long time or loop.
evaluateScriptRestricting
    :: VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> ExBudget        -- ^ The resource budget which must not be exceeded during evaluation
    -> SerializedScript          -- ^ The script to evaluate
    -> [PLC.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting verbose ectx budget p args = swap $ runWriter @LogOutput $ runExceptT $ do
    appliedTerm <- mkTermToEvaluate p args
    let (res, UPLC.RestrictingSt (PLC.ExRestrictingBudget final), logs) =
            UPLC.runCekDeBruijn
                (toMachineParameters ectx)
                (UPLC.restricting $ PLC.ExRestrictingBudget budget)
                (if verbose == Verbose then UPLC.logEmitter else UPLC.noEmitter)
                appliedTerm

    tell logs
    liftEither $ first CekError $ void res
    pure (budget `PLC.minusExBudget` final)

-- | Evaluates a script, returning the minimum budget that the script would need
-- to evaluate successfully. This will take as long as the script takes, if you need to
-- limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
-- also returns the used budget.
evaluateScriptCounting
    :: VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> SerializedScript          -- ^ The script to evaluate
    -> [PLC.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting verbose ectx p args = swap $ runWriter @LogOutput $ runExceptT $ do
    appliedTerm <- mkTermToEvaluate p args

    let (res, UPLC.CountingSt final, logs) =
            UPLC.runCekDeBruijn
                (toMachineParameters ectx)
                UPLC.counting
                (if verbose == Verbose then UPLC.logEmitter else UPLC.noEmitter)
                appliedTerm

    tell logs
    liftEither $ first CekError $ void res
    pure final
