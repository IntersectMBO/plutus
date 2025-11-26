-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module PlutusLedgerApi.Common.Eval
  ( EvaluationError (..)
  , EvaluationContext (..)
  , AsScriptDecodeError (..)
  , LogOutput
  , VerboseMode (..)
  , evaluateScriptRestricting
  , evaluateScriptCounting
  , evaluateTerm
  , mkDynEvaluationContext
  , toMachineParameters
  , mkTermToEvaluate
  , assertWellFormedCostModelParams
  ) where

import PlutusCore
import PlutusCore.Builtin (CaserBuiltin)
import PlutusCore.Data as Plutus
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.ExBudget as Plutus
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as Plutus
import PlutusCore.Evaluation.Machine.MachineParameters (MachineParameters (..))
import PlutusCore.Evaluation.Machine.MachineParameters.Default
import PlutusCore.MkPlc qualified as UPLC
import PlutusCore.Pretty
import PlutusLedgerApi.Common.SerialisedScript
import PlutusLedgerApi.Common.Versions
import PlutusPrelude
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

import Control.Lens
import Control.Monad (unless)
import Control.Monad.Error.Lens
import Control.Monad.Except (MonadError (..), liftEither, runExceptT)
import Control.Monad.Writer (MonadWriter (..), runWriter)
import Data.Set as Set
import Data.Text (Text)
import Data.Tuple
import NoThunks.Class

-- | Errors that can be thrown when evaluating a Plutus script.
data EvaluationError
  = -- | An error from the evaluator itself
    CekError !(UPLC.CekEvaluationException NamedDeBruijn DefaultUni DefaultFun)
  | -- | An error in the pre-evaluation step of converting from de-Bruijn indices
    DeBruijnError !FreeVariableError
  | {-| A deserialisation error
    TODO: make this error more informative when we have more information about what went wrong -}
    CodecError !ScriptDecodeError
  | -- | An error indicating that the cost model parameters didn't match what we expected
    CostModelParameterMismatch
  | -- | The script evaluated to a value that is not a valid return value.
    InvalidReturnValue
  deriving stock (Show, Eq)

makeClassyPrisms ''EvaluationError

instance AsScriptDecodeError EvaluationError where
  _ScriptDecodeError = _CodecError

instance Pretty EvaluationError where
  pretty (CekError e) = prettyClassic e
  pretty (DeBruijnError e) = pretty e
  pretty (CodecError e) = pretty e
  pretty CostModelParameterMismatch = "Cost model parameters were not as we expected"
  pretty InvalidReturnValue =
    "The evaluation finished but the result value is not valid. "
      <> "Plutus V3 scripts must return BuiltinUnit. "
      <> "Returning any other value is considered a failure."

-- | A simple toggle indicating whether or not we should accumulate logs during script execution.
data VerboseMode
  = -- | accumulate all traces
    Verbose
  | -- | don't accumulate anything
    Quiet
  deriving stock (Eq)

{-| The type of the executed script's accumulated log output: a list of 'Text'.

It will be an empty list if the `VerboseMode` is set to `Quiet`. -}
type LogOutput = [Text]

{-| Shared helper for the evaluation functions: 'evaluateScriptCounting' and 'evaluateScriptRestricting',

Given a 'ScriptForEvaluation':

1) applies the term to a list of 'Data' arguments (e.g. Datum, Redeemer, `ScriptContext`)
2) checks that the applied-term is well-scoped
3) returns the applied-term -}
mkTermToEvaluate
  :: MonadError EvaluationError m
  => PlutusLedgerLanguage
  -- ^ the Plutus ledger language of the script under execution.
  -> MajorProtocolVersion
  -- ^ which major protocol version to run the operation in
  -> ScriptForEvaluation
  -- ^ the script to evaluate
  -> [Plutus.Data]
  -- ^ the arguments that the script's underlying term will be applied to
  -> m (UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ())
mkTermToEvaluate ll pv script args = do
  let ScriptNamedDeBruijn (UPLC.Program _ v t) = deserialisedScript script
      termArgs = fmap (UPLC.mkConstant ()) args
      appliedT = UPLC.mkIterAppNoAnn t termArgs

  -- check that the Plutus Core language version is available
  -- See Note [Checking the Plutus Core language version]
  unless (v `Set.member` plcVersionsAvailableIn ll pv) $
    throwing _ScriptDecodeError $
      PlutusCoreLanguageNotAvailableError v ll pv

  -- make sure that term is closed, i.e. well-scoped
  through (liftEither . first DeBruijnError . UPLC.checkScope) appliedT

toMachineParameters :: MajorProtocolVersion -> EvaluationContext -> DefaultMachineParameters
toMachineParameters pv (EvaluationContext ll toCaser toSemVar machParsList) =
  case lookup (toSemVar pv) machParsList of
    Nothing ->
      error $
        Prelude.concat
          ["Internal error: ", show ll, " does not support protocol version ", show pv]
    Just machVarPars -> MachineParameters (toCaser pv) machVarPars

{-| An opaque type that contains all the static parameters that the evaluator needs to evaluate a
script. This is so that they can be computed once and cached, rather than being recomputed on every
evaluation.

Different protocol versions may require different bundles of machine parameters, which allows us for
example to tweak the shape of the costing function of a builtin, so that the builtin costs less.
Currently this means that we have to create multiple 'DefaultMachineParameters' per language
version, which we put into a cache (represented by an association list) in order to avoid costly
recomputation of machine parameters.

In order to get the appropriate 'DefaultMachineParameters' at validation time we look it up in the
cache using a semantics variant as a key. We compute the semantics variant from the protocol
version using the stored function. Note that the semantics variant depends on the language version
too, but the latter is known statically (because each language version has its own evaluation
context), hence there's no reason to require it to be provided at runtime.

To say it differently, there's a matrix of semantics variants indexed by (LL, PV) pairs and we
cache its particular row corresponding to the statically given LL in an 'EvaluationContext'.

The reason why we associate a 'DefaultMachineParameters' with a semantics variant rather than a
protocol version are

1. generally there are far more protocol versions than semantics variants supported by a specific
   language version, so we save on pointless duplication of bundles of machine parameters
2. builtins don't know anything about protocol versions, only semantics variants. It is therefore
   more semantically precise to associate bundles of machine parameters with semantics variants than
   with protocol versions -}
data EvaluationContext = EvaluationContext
  { _evalCtxLedgerLang :: PlutusLedgerLanguage
  -- ^ Specifies what language versions the 'EvaluationContext' is for.
  , _evalCtxCaserBuiltin :: MajorProtocolVersion -> CaserBuiltin DefaultUni
  {-^ Specifies how 'case' on values of built-in types works: fails evaluation for older
  protocol versions and defers to 'caseBuiltin' for newer ones. Note that this function
  doesn't depend on the 'PlutusLedgerLanguage' or the AST version: deserialisation of a 1.0.0
  AST fails upon encountering a 'Case' node anyway, so we can safely assume here that 'case'
  is available.
  FIXME: do we need to test that it fails for older PVs?  We can't submit
  transactions in old PVs, so maybe it doesn't matter. -}
  , _evalCtxToSemVar :: MajorProtocolVersion -> BuiltinSemanticsVariant DefaultFun
  {-^ Specifies how to get a semantics variant for this ledger language given a
  'MajorProtocolVersion'. -}
  , _evalCtxMachParsCache
      :: [(BuiltinSemanticsVariant DefaultFun, DefaultMachineVariantParameters)]
  {-^ The cache of 'DefaultMachineParameters' for each semantics variant supported by the
  current language version. -}
  }
  deriving stock (Generic)
  deriving anyclass (NFData, NoThunks)

{-|  Create an 'EvaluationContext' given all builtin semantics variants supported by the provided
language version.

The input is a `Map` of `Text`s to cost integer values (aka `Plutus.CostModelParams`, `Alonzo.CostModel`)
See Note [Inlining meanings of builtins].

IMPORTANT: the 'toSemVar' argument computes the semantics variant for each 'MajorProtocolVersion'
and it must only return semantics variants from the 'semVars' list, as well as cover ANY
'MajorProtocolVersion', including those that do not exist yet (i.e. 'toSemVar' must never fail).

IMPORTANT: The evaluation context of every Plutus version must be recreated upon a protocol update
with the updated cost model parameters. -}
mkDynEvaluationContext
  :: MonadError CostModelApplyError m
  => PlutusLedgerLanguage
  -> (MajorProtocolVersion -> CaserBuiltin DefaultUni)
  -> [BuiltinSemanticsVariant DefaultFun]
  -> (MajorProtocolVersion -> BuiltinSemanticsVariant DefaultFun)
  -> Plutus.CostModelParams
  -> m EvaluationContext
mkDynEvaluationContext ll toCaser semVars toSemVar newCMP = do
  machPars <- mkMachineVariantParametersFor semVars newCMP
  pure $ EvaluationContext ll toCaser toSemVar machPars

-- FIXME (https://github.com/IntersectMBO/plutus-private/issues/1726): remove this function
assertWellFormedCostModelParams :: MonadError CostModelApplyError m => Plutus.CostModelParams -> m ()
assertWellFormedCostModelParams = void . Plutus.applyCostModelParams Plutus.defaultCekCostModelForTesting

{-| Evaluate a fully-applied term using the CEK machine. Useful for mimicking the behaviour of the
on-chain evaluator. -}
evaluateTerm
  :: UPLC.ExBudgetMode cost DefaultUni DefaultFun
  -> MajorProtocolVersion
  -> VerboseMode
  -> EvaluationContext
  -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
  -> UPLC.CekReport cost NamedDeBruijn DefaultUni DefaultFun
evaluateTerm budgetMode pv verbose ectx =
  UPLC.runCekDeBruijn
    (toMachineParameters pv ectx)
    budgetMode
    (if verbose == Verbose then UPLC.logEmitter else UPLC.noEmitter)
-- Just replicating the old behavior, probably doesn't matter.
{-# INLINE evaluateTerm #-}

{-| Evaluates a script, with a cost model and a budget that restricts how many
resources it can use according to the cost model. Also returns the budget that
was actually used.

Can be used to calculate budgets for scripts, but even in this case you must give
a limit to guard against scripts that run for a long time or loop.

Note: Parameterized over the 'LedgerPlutusVersion' since
1. The builtins allowed (during decoding) differ, and
2. The Plutus language versions allowed differ. -}
evaluateScriptRestricting
  :: PlutusLedgerLanguage
  -- ^ The Plutus ledger language of the script under execution.
  -> MajorProtocolVersion
  -- ^ Which major protocol version to run the operation in
  -> VerboseMode
  -- ^ Whether to produce log output
  -> EvaluationContext
  -- ^ Includes the cost model to use for tallying up the execution costs
  -> ExBudget
  -- ^ The resource budget which must not be exceeded during evaluation
  -> ScriptForEvaluation
  -- ^ The script to evaluate
  -> [Plutus.Data]
  -- ^ The arguments to the script
  -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting ll pv verbose ectx budget p args = swap $ runWriter @LogOutput $ runExceptT $ do
  appliedTerm <- mkTermToEvaluate ll pv p args
  let UPLC.CekReport res (UPLC.RestrictingSt (ExRestrictingBudget final)) logs =
        evaluateTerm (UPLC.restricting $ ExRestrictingBudget budget) pv verbose ectx appliedTerm
  processLogsAndErrors ll logs res
  pure (budget `minusExBudget` final)

{-| Evaluates a script, returning the minimum budget that the script would need
to evaluate successfully. This will take as long as the script takes, if you need to
limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
also returns the used budget.

Note: Parameterized over the ledger-plutus-version since the builtins allowed (during decoding) differs. -}
evaluateScriptCounting
  :: PlutusLedgerLanguage
  -- ^ The Plutus ledger language of the script under execution.
  -> MajorProtocolVersion
  -- ^ Which major protocol version to run the operation in
  -> VerboseMode
  -- ^ Whether to produce log output
  -> EvaluationContext
  -- ^ Includes the cost model to use for tallying up the execution costs
  -> ScriptForEvaluation
  -- ^ The script to evaluate
  -> [Plutus.Data]
  -- ^ The arguments to the script
  -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting ll pv verbose ectx p args = swap $ runWriter @LogOutput $ runExceptT $ do
  appliedTerm <- mkTermToEvaluate ll pv p args
  let UPLC.CekReport res (UPLC.CountingSt final) logs =
        evaluateTerm UPLC.counting pv verbose ectx appliedTerm
  processLogsAndErrors ll logs res
  pure final

processLogsAndErrors
  :: forall m
   . (MonadError EvaluationError m, MonadWriter LogOutput m)
  => PlutusLedgerLanguage
  -> LogOutput
  -> UPLC.CekResult NamedDeBruijn DefaultUni DefaultFun
  -> m ()
processLogsAndErrors ll logs res = do
  tell logs
  case res of
    UPLC.CekFailure err -> throwError $ CekError err
    -- If evaluation result is '()', then that's correct for all Plutus versions.
    UPLC.CekSuccessConstant (Some (ValueOf DefaultUniUnit ())) -> pure ()
    -- If evaluation result is any other constant or term, then it's only correct for V1 and V2.
    UPLC.CekSuccessConstant {} -> handleOldVersions
    UPLC.CekSuccessNonConstant {} -> handleOldVersions
  where
    handleOldVersions = unless (ll == PlutusV1 || ll == PlutusV2) $ throwError InvalidReturnValue
{-# INLINE processLogsAndErrors #-}

{- Note [Checking the Plutus Core language version]
Since long ago this check has been in `mkTermToEvaluate`, which makes it a phase 2 failure.
But this is really far too strict: we can check when deserializing, so it can be a phase 1
failure, like the other such checks that we have. For now we keep it as it is, but we may
try to move it later.
-}
