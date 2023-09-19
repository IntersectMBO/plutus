-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

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
import PlutusCore.Data as Plutus
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.ExBudget as Plutus
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as Plutus
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
import Data.Text as Text
import Data.Tuple
import NoThunks.Class
import Prettyprinter

-- | Errors that can be thrown when evaluating a Plutus script.
data EvaluationError =
    CekError !(UPLC.CekEvaluationException NamedDeBruijn DefaultUni DefaultFun) -- ^ An error from the evaluator itself
    | DeBruijnError !FreeVariableError -- ^ An error in the pre-evaluation step of converting from de-Bruijn indices
    | CodecError !ScriptDecodeError -- ^ A deserialisation error
    -- TODO: make this error more informative when we have more information about what went wrong
    | CostModelParameterMismatch -- ^ An error indicating that the cost model parameters didn't match what we expected
    deriving stock (Show, Eq)
makeClassyPrisms ''EvaluationError

instance AsScriptDecodeError EvaluationError where
    _ScriptDecodeError = _CodecError

instance Pretty EvaluationError where
    pretty (CekError e)               = prettyClassicDef e
    pretty (DeBruijnError e)          = pretty e
    pretty (CodecError e)             = viaShow e
    pretty CostModelParameterMismatch = "Cost model parameters were not as we expected"

-- | A simple toggle indicating whether or not we should accumulate logs during script execution.
data VerboseMode =
    Verbose -- ^ accumulate all traces
    | Quiet -- ^ don't accumulate anything
    deriving stock (Eq)

{-| The type of the executed script's accumulated log output: a list of 'Text'.

It will be an empty list if the `VerboseMode` is set to `Quiet`.
-}
type LogOutput = [Text.Text]

{-| Shared helper for the evaluation functions: 'evaluateScriptCounting' and 'evaluateScriptRestricting',

Given a 'ScriptForEvaluation':

1) applies the term to a list of 'Data' arguments (e.g. Datum, Redeemer, `ScriptContext`)
2) checks that the applied-term is well-scoped
3) returns the applied-term
-}
mkTermToEvaluate
    :: (MonadError EvaluationError m)
    => PlutusLedgerLanguage -- ^ the Plutus ledger language of the script under execution.
    -> MajorProtocolVersion -- ^ which major protocol version to run the operation in
    -> ScriptForEvaluation -- ^ the script to evaluate
    -> [Plutus.Data] -- ^ the arguments that the script's underlying term will be applied to
    -> m (UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ())
mkTermToEvaluate ll pv script args = do
    let ScriptNamedDeBruijn (UPLC.Program _ v t) = deserialisedScript script
        termArgs = fmap (UPLC.mkConstant ()) args
        appliedT = UPLC.mkIterAppNoAnn t termArgs

    -- check that the Plutus Core language version is available
    -- See Note [Checking the Plutus Core language version]
    unless (v `Set.member` plcVersionsAvailableIn ll pv) $ throwing _ScriptDecodeError $ PlutusCoreLanguageNotAvailableError v pv

    -- make sure that term is closed, i.e. well-scoped
    through (liftEither . first DeBruijnError . UPLC.checkScope) appliedT

toMachineParameters :: MajorProtocolVersion -> EvaluationContext -> DefaultMachineParameters
toMachineParameters _ = machineParameters

{-| An opaque type that contains all the static parameters that the evaluator needs to evaluate a
script.  This is so that they can be computed once and cached, rather than being recomputed on every
evaluation.
-}
newtype EvaluationContext = EvaluationContext
    { machineParameters :: DefaultMachineParameters
    }
    deriving stock Generic
    deriving anyclass (NFData, NoThunks)

{-|  Create an 'EvaluationContext' for a given builtin semantics variant.

The input is a `Map` of `Text`s to cost integer values (aka `Plutus.CostModelParams`, `Alonzo.CostModel`)
See Note [Inlining meanings of builtins].

IMPORTANT: The evaluation context of every Plutus version must be recreated upon a protocol update
with the updated cost model parameters.
-}
mkDynEvaluationContext
    :: MonadError CostModelApplyError m
    => BuiltinSemanticsVariant DefaultFun
    -> Plutus.CostModelParams
    -> m EvaluationContext
mkDynEvaluationContext semvar newCMP =
    EvaluationContext <$> mkMachineParametersFor semvar newCMP

-- FIXME: remove this function
assertWellFormedCostModelParams :: MonadError CostModelApplyError m => Plutus.CostModelParams -> m ()
assertWellFormedCostModelParams = void . Plutus.applyCostModelParams Plutus.defaultCekCostModel

-- | Evaluate a fully-applied term using the CEK machine. Useful for mimicking the behaviour of the
-- on-chain evaluator.
evaluateTerm
    :: UPLC.ExBudgetMode cost DefaultUni DefaultFun
    -> MajorProtocolVersion
    -> VerboseMode
    -> EvaluationContext
    -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
    -> ( Either
            (UPLC.CekEvaluationException NamedDeBruijn DefaultUni DefaultFun)
            (UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ())
       , cost
       , [Text]
       )
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
2. The Plutus language versions allowed differ.
-}
evaluateScriptRestricting
    :: PlutusLedgerLanguage -- ^ The Plutus ledger language of the script under execution.
    -> MajorProtocolVersion -- ^ Which major protocol version to run the operation in
    -> VerboseMode          -- ^ Whether to produce log output
    -> EvaluationContext    -- ^ Includes the cost model to use for tallying up the execution costs
    -> ExBudget             -- ^ The resource budget which must not be exceeded during evaluation
    -> ScriptForEvaluation  -- ^ The script to evaluate
    -> [Plutus.Data]        -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting ll pv verbose ectx budget p args = swap $ runWriter @LogOutput $ runExceptT $ do
    appliedTerm <- mkTermToEvaluate ll pv p args
    let (res, UPLC.RestrictingSt (ExRestrictingBudget final), logs) =
            evaluateTerm (UPLC.restricting $ ExRestrictingBudget budget) pv verbose ectx appliedTerm
    tell logs
    liftEither $ first CekError $ void res
    pure (budget `minusExBudget` final)

{-| Evaluates a script, returning the minimum budget that the script would need
to evaluate successfully. This will take as long as the script takes, if you need to
limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
also returns the used budget.

Note: Parameterized over the ledger-plutus-version since the builtins allowed (during decoding) differs.
-}
evaluateScriptCounting
    :: PlutusLedgerLanguage -- ^ The Plutus ledger language of the script under execution.
    -> MajorProtocolVersion -- ^ Which major protocol version to run the operation in
    -> VerboseMode          -- ^ Whether to produce log output
    -> EvaluationContext    -- ^ Includes the cost model to use for tallying up the execution costs
    -> ScriptForEvaluation  -- ^ The script to evaluate
    -> [Plutus.Data]        -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting ll pv verbose ectx p args = swap $ runWriter @LogOutput $ runExceptT $ do
    appliedTerm <- mkTermToEvaluate ll pv p args
    let (res, UPLC.CountingSt final, logs) =
            evaluateTerm UPLC.counting pv verbose ectx appliedTerm
    tell logs
    liftEither $ first CekError $ void res
    pure final

{- Note [Checking the Plutus Core language version]
Since long ago this check has been in `mkTermToEvaluate`, which makes it a phase 2 failure.
But this is really far too strict: we can check when deserializing, so it can be a phase 1
failure, like the other such checks that we have. For now we keep it as it is, but we may
try to move it later.
-}

-- TODO: Remove after https://github.com/input-output-hk/nothunks/pull/34
deriving anyclass instance NoThunks a => NoThunks (Identity a)
