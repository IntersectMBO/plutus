{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

{-# LANGUAGE StrictData        #-}

-- GHC is asked to do quite a lot of optimization in this module, so we're increasing the amount of
-- ticks for the simplifier not to run out of them.
{-# OPTIONS_GHC -fsimpl-tick-factor=200 #-}

-- | Common types and functions used across all the ledger API modules.
module Plutus.ApiCommon where

import PlutusCore as Plutus hiding (Version)
import PlutusCore as ScriptPlutus (Version)
import PlutusCore.Data as Plutus
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.ExBudget as Plutus
import PlutusCore.Evaluation.Machine.MachineParameters as Plutus
import PlutusCore.MkPlc qualified as UPLC
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Check.Scope qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

import Codec.CBOR.Decoding qualified as CBOR
import Codec.CBOR.Extras
import Codec.CBOR.Read qualified as CBOR
import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.Writer
import Data.Bifunctor
import Data.ByteString.Lazy (fromStrict)
import Data.ByteString.Short
import Data.Coerce
import Data.Either
import Data.Foldable (fold)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Text
import Data.Tuple
import GHC.Exts (inline)
import GHC.Generics
import NoThunks.Class
import PlutusCore.Pretty
import PlutusPrelude (through)
import Prettyprinter

{- Note [New builtins and protocol versions]
When we add a new builtin to the language, that is a *backwards-compatible* change.
Old scripts will still work (since they don't use the new builtins), we just make some more
scripts possible.

It would be nice, therefore, to get away with just having one definition of the set of builtin
functions. Then the new builtins will just "work". However, this neglects the fact that
the new builtins will be added to the builtin universe in the *software update* that
brings a new version of Plutus, but they should only be usable after the corresponding
*hard fork*. So there is a period of time in which they must be present in the software but not
usable, so we need to decide this conditionally based on the protocol version.

To do this we need to:
- Know which protocol version a builtin was introduced in.
- Given the protocol version, check a program for builtins that should not be usable yet.

Note that this doesn't currently handle removals of builtins, although it fairly straighforwardly
could do, just by tracking when they were removed.
-}

{- Note [Size checking of constants in PLC programs]
We impose a 64-byte *on-the-wire* limit on the constants inside PLC programs. This prevents people from inserting
Mickey Mouse entire.

This is somewhat inconvenient for users, but they can always send multiple bytestrings and
concatenate them at runtime.

Unfortunately this check was broken in the ledger Plutus language version V1, and so for backwards compatibility
we only perform it in V2 and above.
-}

{- Note [Inlining meanings of builtins]
It's vitally important to inline the 'toBuiltinMeaning' method of a set of built-in functions as
that allows GHC to look under lambdas and completely optimize multiple abstractions away.

There are two ways of doing that: by relying on 'INLINE' pragmas all the way up from the
'ToBuiltinMeaning' instance for the default set of builtins or by ensuring that 'toBuiltinsRuntime'
is compiled efficient by turning it into a one-method class (see
https://github.com/input-output-hk/plutus/pull/4419 for how that looks like). We chose the former,
because it's simpler. Although it's also less reliable: machine parameters are computed in
multiple places and we need to make sure that benchmarking, cost model calculations and the actual
production path have builtins compiled in the same way, 'cause otherwise performance analysis and
cost predictions can be wrong by a big margin without us knowing. Because of this danger in addition
to putting @INLINE@ pragmas on every relevant definition, we also stick a call to 'inline' at the
call site. We also do not attempt to only compile things efficiently where we need that and instead
inline the meanins of builtins everywhere. Just to be sure.

Note that a combination of @INLINABLE@ + 'inline' does not result in proper inlining for whatever
reason. It has to be @INLINE@ (and we add 'inline' on top of that for some additional reliability
as we did have cases where sticking 'inline' on something that already had @INLINE@ would fix
inlining).
-}

-- | Scripts to the ledger are serialised bytestrings.
type SerializedScript = ShortByteString

-- | The plutus language version as seen from the ledger's side.
-- Note: the ordering of constructors matters for deriving Ord
data LedgerPlutusVersion = PlutusV1
                         | PlutusV2
   deriving stock (Eq, Ord)

-- | This represents the Cardano protocol version, with its major and minor components.
-- This relies on careful understanding between us and the ledger as to what this means.
data ProtocolVersion = ProtocolVersion { pvMajor :: Int, pvMinor :: Int }
  deriving stock (Show, Eq)

instance Ord ProtocolVersion where
    -- same as deriving Ord, just for having it explicitly
    compare (ProtocolVersion major minor) (ProtocolVersion major' minor') = compare major major' <> compare minor minor'

instance Pretty ProtocolVersion where
    pretty (ProtocolVersion major minor) = pretty major <> "." <> pretty minor

{-| A map indicating which builtin functions were introduced in which 'ProtocolVersion'. Each builtin function should appear at most once.

This *must* be updated when new builtins are added.
See Note [New builtins and protocol versions]
-}
builtinsIntroducedIn :: Map.Map (LedgerPlutusVersion, ProtocolVersion) (Set.Set DefaultFun)
builtinsIntroducedIn = Map.fromList [
  -- 5.0 is Alonzo
  ((PlutusV1, ProtocolVersion 5 0), Set.fromList [
          AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, QuotientInteger, RemainderInteger, ModInteger, EqualsInteger, LessThanInteger, LessThanEqualsInteger,
          AppendByteString, ConsByteString, SliceByteString, LengthOfByteString, IndexByteString, EqualsByteString, LessThanByteString, LessThanEqualsByteString,
          Sha2_256, Sha3_256, Blake2b_256, VerifyEd25519Signature,
          AppendString, EqualsString, EncodeUtf8, DecodeUtf8,
          IfThenElse,
          ChooseUnit,
          Trace,
          FstPair, SndPair,
          ChooseList, MkCons, HeadList, TailList, NullList,
          ChooseData, ConstrData, MapData, ListData, IData, BData, UnConstrData, UnMapData, UnListData, UnIData, UnBData, EqualsData,
          MkPairData, MkNilData, MkNilPairData
          ]),
  ((PlutusV2, ProtocolVersion 7 0), Set.fromList [
          SerialiseData
          ]),
  ((PlutusV2, ProtocolVersion 8 0), Set.fromList [
          VerifyEcdsaSecp256k1Signature, VerifySchnorrSecp256k1Signature
          ])
  ]

{-| Which builtin functions are available in the given 'ProtocolVersion'?

See Note [New builtins and protocol versions]
-}
builtinsAvailableIn :: LedgerPlutusVersion -> ProtocolVersion -> Set.Set DefaultFun
builtinsAvailableIn thisLv thisPv = fold $ Map.elems $
    Map.takeWhileAntitone builtinAvailableIn builtinsIntroducedIn
    where
      builtinAvailableIn :: (LedgerPlutusVersion, ProtocolVersion) -> Bool
      builtinAvailableIn (introducedInLv,introducedInPv) =
          -- both should be satisfied
          introducedInLv <= thisLv && introducedInPv <= thisPv

-- | A variant of `Script` with a specialized decoder.
newtype ScriptForExecution = ScriptForExecution (UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ())

{-| This decoder decodes the names directly into `NamedDeBruijn`s rather than `DeBruijn`s.
This is needed because the CEK machine expects `NameDeBruijn`s, but there are obviously no names in the serialized form of a `Script`.
Rather than traversing the term and inserting fake names after deserializing, this lets us do at the same time as deserializing.
-}
scriptCBORDecoder :: LedgerPlutusVersion -> ProtocolVersion -> CBOR.Decoder s ScriptForExecution
scriptCBORDecoder lv pv =
    -- See Note [New builtins and protocol versions]
    let availableBuiltins = builtinsAvailableIn lv pv
        -- TODO: optimize this by using a better datastructure e.g. 'IntSet'
        flatDecoder = UPLC.decodeProgram (\f -> f `Set.member` availableBuiltins)
    in do
        -- Deserialize using 'FakeNamedDeBruijn' to get the fake names added
        (p :: UPLC.Program UPLC.FakeNamedDeBruijn DefaultUni DefaultFun ()) <- decodeViaFlat flatDecoder
        pure $ coerce p

{-| Check if a 'Script' is "valid" according to a protocol version. At the moment this means "deserialises correctly", which in particular
implies that it is (almost certainly) an encoded script and the script does not mention any builtins unavailable in the given protocol version.

Note: Parameterized over the ledger-plutus-version since the builtins allowed (during decoding) differs.
-}
isScriptWellFormed :: LedgerPlutusVersion -> ProtocolVersion -> SerializedScript -> Bool
isScriptWellFormed lv pv = isRight . CBOR.deserialiseFromBytes (scriptCBORDecoder lv pv) . fromStrict . fromShort

-- | Errors that can be thrown when evaluating a Plutus script.
data EvaluationError =
    CekError (UPLC.CekEvaluationException NamedDeBruijn DefaultUni DefaultFun) -- ^ An error from the evaluator itself
    | DeBruijnError FreeVariableError -- ^ An error in the pre-evaluation step of converting from de-Bruijn indices
    | CodecError CBOR.DeserialiseFailure -- ^ A serialisation error
    | IncompatibleVersionError (ScriptPlutus.Version ()) -- ^ An error indicating a version tag that we don't support
    -- TODO: make this error more informative when we have more information about what went wrong
    | CostModelParameterMismatch -- ^ An error indicating that the cost model parameters didn't match what we expected
    deriving stock (Show, Eq)

instance Pretty EvaluationError where
    pretty (CekError e)      = prettyClassicDef e
    pretty (DeBruijnError e) = pretty e
    pretty (CodecError e) = viaShow e
    pretty (IncompatibleVersionError actual) = "This version of the Plutus Core interface does not support the version indicated by the AST:" <+> pretty actual
    pretty CostModelParameterMismatch = "Cost model parameters were not as we expected"

-- | The type of log output: just a list of 'Text'.
type LogOutput = [Text]

-- | A simple toggle indicating whether or not we should produce logs.
data VerboseMode = Verbose | Quiet
    deriving stock (Eq)

-- | Shared helper for the evaluation functions, deserializes the 'SerializedScript' , applies it to its arguments, puts fakenamedebruijns, and scope-checks it.
mkTermToEvaluate
    :: (MonadError EvaluationError m)
    => LedgerPlutusVersion
    -> ProtocolVersion
    -> SerializedScript
    -> [Plutus.Data]
    -> m (UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ())
mkTermToEvaluate lv pv bs args = do
    -- It decodes the program through the optimized ScriptForExecution. See `ScriptForExecution`.
    (_, ScriptForExecution (UPLC.Program _ v t)) <- liftEither $ first CodecError $ CBOR.deserialiseFromBytes (scriptCBORDecoder lv pv) $ fromStrict $ fromShort bs
    unless (v == Plutus.defaultVersion ()) $ throwError $ IncompatibleVersionError v
    let termArgs = fmap (UPLC.mkConstant ()) args
        appliedT = UPLC.mkIterApp () t termArgs

    -- make sure that term is closed, i.e. well-scoped
    through (liftEither . first DeBruijnError . UPLC.checkScope) appliedT

-- | Which unlifting mode should we use in the given 'ProtocolVersion'
-- so as to correctly construct the machine's parameters
unliftingModeIn :: ProtocolVersion -> UnliftingMode
unliftingModeIn pv =
    -- This just changes once in version 7.0
    if pv >= ProtocolVersion 7 0 then UnliftingDeferred else UnliftingImmediate

type DefaultMachineParameters = MachineParameters CekMachineCosts UPLC.CekValue DefaultUni DefaultFun

toMachineParameters :: ProtocolVersion -> EvaluationContext -> DefaultMachineParameters
toMachineParameters pv = case unliftingModeIn pv of
    UnliftingImmediate -> machineParametersImmediate
    UnliftingDeferred  -> machineParametersDeferred

mkMachineParametersFor :: (MonadError CostModelApplyError m)
                       => UnliftingMode
                       -> Plutus.CostModelParams
                       -> m DefaultMachineParameters
mkMachineParametersFor unlMode newCMP =
    inline Plutus.mkMachineParameters unlMode <$>
        Plutus.applyCostModelParams Plutus.defaultCekCostModel newCMP
{-# INLINE mkMachineParametersFor #-}


{-| An opaque type that contains all the static parameters that the evaluator needs to evaluate a
script.  This is so that they can be computed once and cached, rather than recomputed on every
evaluation.

There are two sets of parameters: one is with immediate unlifting and the other one is with
deferred unlifting. We have to keep both of them, because depending on the language version
 either one has to be used or the other. We also compile them separately due to all the inlining
 and optimization that need to happen for things to be efficient.
-}
data EvaluationContext = EvaluationContext
    { machineParametersImmediate :: DefaultMachineParameters
    , machineParametersDeferred  :: DefaultMachineParameters
    }
    deriving stock Generic
    deriving anyclass (NFData, NoThunks)

{-|  Build the 'EvaluationContext'.

The input is a `Map` of strings to cost integer values (aka `Plutus.CostModelParams`, `Alonzo.CostModel`)
See Note [Inlining meanings of builtins].
-}
mkEvaluationContext :: MonadError CostModelApplyError m => Plutus.CostModelParams -> m EvaluationContext
mkEvaluationContext newCMP =
    EvaluationContext
        <$> inline mkMachineParametersFor UnliftingImmediate newCMP
        <*> inline mkMachineParametersFor UnliftingDeferred newCMP

-- | Comparably expensive to `mkEvaluationContext`, so it should only be used sparingly.
assertWellFormedCostModelParams :: MonadError CostModelApplyError m => Plutus.CostModelParams -> m ()
assertWellFormedCostModelParams = void . Plutus.applyCostModelParams Plutus.defaultCekCostModel

{-|
Evaluates a script, with a cost model and a budget that restricts how many
resources it can use according to the cost model. Also returns the budget that
was actually used.

Can be used to calculate budgets for scripts, but even in this case you must give
a limit to guard against scripts that run for a long time or loop.

Note: Parameterized over the ledger-plutus-version since the builtins allowed (during decoding) differs.
-}
evaluateScriptRestricting
    :: LedgerPlutusVersion
    -> ProtocolVersion
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> ExBudget        -- ^ The resource budget which must not be exceeded during evaluation
    -> SerializedScript          -- ^ The script to evaluate
    -> [Plutus.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting lv pv verbose ectx budget p args = swap $ runWriter @LogOutput $ runExceptT $ do
    appliedTerm <- mkTermToEvaluate lv pv p args

    let (res, UPLC.RestrictingSt (ExRestrictingBudget final), logs) =
            UPLC.runCekDeBruijn
                (toMachineParameters pv ectx)
                (UPLC.restricting $ ExRestrictingBudget budget)
                (if verbose == Verbose then UPLC.logEmitter else UPLC.noEmitter)
                appliedTerm

    tell logs
    liftEither $ first CekError $ void res
    pure (budget `minusExBudget` final)

{-|
Evaluates a script, returning the minimum budget that the script would need
to evaluate successfully. This will take as long as the script takes, if you need to
limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
also returns the used budget.

Note: Parameterized over the ledger-plutus-version since the builtins allowed (during decoding) differs.
-}
evaluateScriptCounting
    :: LedgerPlutusVersion
    -> ProtocolVersion
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> SerializedScript          -- ^ The script to evaluate
    -> [Plutus.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting lv pv verbose ectx p args = swap $ runWriter @LogOutput $ runExceptT $ do
    appliedTerm <- mkTermToEvaluate lv pv p args

    let (res, UPLC.CountingSt final, logs) =
            UPLC.runCekDeBruijn
                (toMachineParameters pv ectx)
                UPLC.counting
                (if verbose == Verbose then UPLC.logEmitter else UPLC.noEmitter)
                appliedTerm

    tell logs
    liftEither $ first CekError $ void res
    pure final
