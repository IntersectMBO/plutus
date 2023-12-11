-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module PlutusIR.Compiler (
    compileProgram,
    compileToReadable,
    compileReadableToPlc,
    Compiling,
    Error (..),
    AsError (..),
    AsTypeError (..),
    AsTypeErrorExt (..),
    Provenance (..),
    DatatypeComponent (..),
    noProvenance,
    CompilationOpts (..),
    coOptimize,
    coTypecheck,
    coPedantic,
    coVerbose,
    coDebug,
    coMaxSimplifierIterations,
    coDoSimplifierUnwrapCancel,
    coDoSimplifierBeta,
    coDoSimplifierInline,
    coDoSimplifierEvaluateBuiltins,
    coDoSimplifierStrictifyBindings,
    coDoSimplifierRewrite,
    coDoSimplifierKnownCon,
    coInlineHints,
    coProfile,
    coRelaxedFloatin,
    coCaseOfCaseConservative,
    coPreserveLogging,
    coDatatypes,
    dcoStyle,
    DatatypeStyle (..),
    defaultCompilationOpts,
    CompilationCtx,
    ccOpts,
    ccEnclosing,
    ccTypeCheckConfig,
    ccBuiltinsInfo,
    ccBuiltinCostModel,
    PirTCConfig(..),
    AllowEscape(..),
    toDefaultCompilationCtx,
    runPass,
    simplifier
    ) where

import Control.Lens
import Control.Monad
import Control.Monad.Except
import Control.Monad.Extra (orM, whenM)
import Data.Monoid
import Data.Monoid.Extra (mwhen)
import Debug.Trace (traceM)
import PlutusCore qualified as PLC
import PlutusCore.Error (throwingEither)
import PlutusIR
import PlutusIR.Compiler.Let qualified as Let
import PlutusIR.Compiler.Lower
import PlutusIR.Compiler.Provenance
import PlutusIR.Compiler.Types
import PlutusIR.Error
import PlutusIR.Pass qualified as P
import PlutusIR.Transform.Beta qualified as Beta
import PlutusIR.Transform.CaseOfCase qualified as CaseOfCase
import PlutusIR.Transform.CaseReduce qualified as CaseReduce
import PlutusIR.Transform.DeadCode qualified as DeadCode
import PlutusIR.Transform.EvaluateBuiltins qualified as EvaluateBuiltins
import PlutusIR.Transform.Inline.Inline qualified as Inline
import PlutusIR.Transform.KnownCon qualified as KnownCon
import PlutusIR.Transform.LetFloatIn qualified as LetFloatIn
import PlutusIR.Transform.LetFloatOut qualified as LetFloatOut
import PlutusIR.Transform.LetMerge qualified as LetMerge
import PlutusIR.Transform.NonStrict qualified as NonStrict
import PlutusIR.Transform.RecSplit qualified as RecSplit
import PlutusIR.Transform.Rename ()
import PlutusIR.Transform.RewriteRules qualified as RewriteRules
import PlutusIR.Transform.StrictifyBindings qualified as StrictifyBindings
import PlutusIR.Transform.ThunkRecursions qualified as ThunkRec
import PlutusIR.Transform.Unwrap qualified as Unwrap
import PlutusPrelude

isVerbose :: Compiling m e uni fun a => m Bool
isVerbose = view $ ccOpts . coVerbose

isDebug :: Compiling m e uni fun a => m Bool
isDebug = view $ ccOpts . coDebug

logVerbose :: Compiling m e uni fun a => String -> m ()
logVerbose = whenM (orM [isVerbose, isDebug]) . traceM

logDebug :: Compiling m e uni fun a => String -> m ()
logDebug = whenM isDebug . traceM

runPass :: (Compiling m e uni fun a, b ~ Provenance a) => m (P.Pass m tyname name uni fun b) -> Term tyname name uni fun b -> m (Term tyname name uni fun b)
runPass mpasses t = do
  passes <- mpasses
  pedantic <- view (ccOpts . coPedantic)
  res <- runExceptT $ P.runPass logVerbose pedantic passes t
  throwingEither _Error res

simplifierPasses :: Compiling m e uni fun a => String -> m (P.Pass m TyName Name uni fun (Provenance a))
simplifierPasses suffix = do
  opts <- view ccOpts
  tcconfig <- view ccTypeCheckConfig
  binfo <- view ccBuiltinsInfo
  costModel <- view ccBuiltinCostModel
  hints <- view (ccOpts . coInlineHints)
  preserveLogging <- view (ccOpts . coPreserveLogging)
  cocConservative <- view (ccOpts . coCaseOfCaseConservative)
  rules <- view ccRewriteRules

  let
    uc = [Unwrap.unwrapCancelPass tcconfig | opts ^. coDoSimplifierUnwrapCancel]
    cr = [CaseReduce.caseReducePass tcconfig | opts ^. coDoSimplifierCaseReduce]
    coc = [CaseOfCase.caseOfCasePassSC tcconfig binfo cocConservative noProvenance | opts ^. coDoSimplifierCaseReduce]
    cokc = [KnownCon.knownConPassSC tcconfig | opts ^. coDoSimplifierKnownCon ]
    beta = [Beta.betaPassSC tcconfig | opts ^. coDoSimplifierBeta ]
    sb = [StrictifyBindings.strictifyBindingsPass tcconfig binfo | opts ^. coDoSimplifierStrictifyBindings ]
    eb = [EvaluateBuiltins.evaluateBuiltinsPass tcconfig preserveLogging binfo costModel | opts ^. coDoSimplifierEvaluateBuiltins ]
    inline = [Inline.inlinePassSC tcconfig hints binfo  | opts ^. coDoSimplifierInline ]
    rw = [RewriteRules.rewritePassSC tcconfig rules | opts ^. coDoSimplifierRewrite ]

  pure $ P.NamedPass ("simplifier" ++ suffix) $ fold (uc ++ cr ++ coc ++ cokc ++ beta ++ sb ++ eb ++ inline ++ rw)

floatOutPasses :: Compiling m e uni fun a => m (P.Pass m TyName Name uni fun (Provenance a))
floatOutPasses = do
  optimize <- view (ccOpts . coOptimize)
  tcconfig <- view ccTypeCheckConfig
  binfo <- view ccBuiltinsInfo
  pure $ mwhen optimize $ P.NamedPass "float-out" $ fold
        [ LetFloatOut.floatTermPassSC tcconfig binfo
        , RecSplit.recSplitPass tcconfig
        , LetMerge.letMergePass tcconfig
        ]

floatInPasses :: Compiling m e uni fun a => m (P.Pass m TyName Name uni fun (Provenance a))
floatInPasses = do
  optimize <- view (ccOpts . coOptimize)
  tcconfig <- view ccTypeCheckConfig
  binfo <- view ccBuiltinsInfo
  relaxed <- view (ccOpts . coRelaxedFloatin)
  pure $ mwhen optimize $ P.NamedPass "float-in" $ fold
        [ LetFloatIn.floatTermPassSC tcconfig binfo relaxed
        , LetMerge.letMergePass tcconfig
        ]

simplifier :: Compiling m e uni fun a => m (P.Pass m TyName Name uni fun (Provenance a))
simplifier = do
  optimize <- view (ccOpts . coOptimize)
  maxIterations <- view (ccOpts . coMaxSimplifierIterations)
  passes <- for [1 .. maxIterations] $ \i -> simplifierPasses (" (pass " ++ show i ++ ")")
  pure $ mwhen optimize $ P.NamedPass "simplifier" (fold passes)

-- | Typecheck a PIR Term iff the context demands it.
-- Note: assumes globally unique names
typeCheckTerm :: (Compiling m e uni fun a) => m (P.Pass m TyName Name uni fun (Provenance a))
typeCheckTerm = do
  doTc <- view (ccOpts . coTypecheck)
  tcconfig <- view ccTypeCheckConfig
  pure $ mwhen doTc $ P.typecheckPass tcconfig

-- | The 1st half of the PIR compiler pipeline up to floating/merging the lets.
-- We stop momentarily here to give a chance to the tx-plugin
-- to dump a "readable" version of pir (i.e. floated).
compileToReadable
  :: forall m e uni fun a b
  . (Compiling m e uni fun a, b ~ Provenance a)
  => Program TyName Name uni fun b
  -> m (Program TyName Name uni fun b)
compileToReadable (Program a v t) = do
  validateOpts v
  let
    pipeline :: m (P.Pass m TyName Name uni fun b)
    pipeline = getAp $ foldMap Ap
        -- We need globally unique names for typechecking, floating, and compiling non-strict bindings
        [ pure P.renamePass
        , typeCheckTerm
        , DeadCode.removeDeadBindingsPassSC <$> view ccTypeCheckConfig <*> view ccBuiltinsInfo
        , simplifier
        , floatOutPasses
        ]
  Program a v <$> runPass pipeline t

-- | The 2nd half of the PIR compiler pipeline.
-- Compiles a 'Term' into a PLC Term, by removing/translating step-by-step the PIR's language constructs to PLC.
-- Note: the result *does* have globally unique names.
compileReadableToPlc :: forall m e uni fun a b . (Compiling m e uni fun a, b ~ Provenance a) => Program TyName Name uni fun b -> m (PLCProgram uni fun a)
compileReadableToPlc (Program a v t) = do

  let
    pipeline :: m (P.Pass m TyName Name uni fun b)
    pipeline = getAp $ foldMap Ap
        [ floatInPasses
        , NonStrict.compileNonStrictBindingsPassSC <$> view ccTypeCheckConfig <*> pure False
        , ThunkRec.thunkRecursionsPass <$> view ccTypeCheckConfig <*> view ccBuiltinsInfo
        -- Process only the non-strict bindings created by 'thunkRecursions' with unit delay/forces
        -- See Note [Using unit versus force/delay]
        , NonStrict.compileNonStrictBindingsPassSC <$> view ccTypeCheckConfig <*> pure True
        , Let.compileLetsPassSC <$> view ccTypeCheckConfig <*> pure Let.DataTypes
        , Let.compileLetsPassSC <$> view ccTypeCheckConfig <*> pure Let.RecTerms
        -- We introduce some non-recursive let bindings while eliminating recursive let-bindings, so we
        -- can eliminate any of them which are unused here.
        , DeadCode.removeDeadBindingsPassSC <$> view ccTypeCheckConfig <*> view ccBuiltinsInfo
        , simplifier
        , Let.compileLetsPassSC <$> view ccTypeCheckConfig <*> pure Let.Types
        , Let.compileLetsPassSC <$> view ccTypeCheckConfig <*> pure Let.NonRecTerms
        ]

    go =
        runPass pipeline
        >=> (<$ logVerbose "  !!! lowerTerm")
        >=> lowerTerm

  PLC.Program a v <$> go t

--- | Compile a 'Program' into a PLC Program. Note: the result *does* have globally unique names.
compileProgram :: Compiling m e uni fun a
            => Program TyName Name uni fun a -> m (PLCProgram uni fun a)
compileProgram =
  (pure . original)
  >=> (<$ logDebug "!!! compileToReadable")
  >=> compileToReadable
  >=> (<$ logDebug "!!! compileReadableToPlc")
  >=> compileReadableToPlc
