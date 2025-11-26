-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module PlutusIR.Compiler
  ( compileProgram
  , compileToReadable
  , compileReadableToPlc
  , Compiling
  , Error (..)
  , Provenance (..)
  , DatatypeComponent (..)
  , noProvenance
  , CompilationOpts (..)
  , coOptimize
  , coTypecheck
  , coPedantic
  , coVerbose
  , coDebug
  , coMaxSimplifierIterations
  , coDoSimplifierUnwrapCancel
  , coDoSimplifierBeta
  , coDoSimplifierInline
  , coDoSimplifierEvaluateBuiltins
  , coDoSimplifierStrictifyBindings
  , coDoSimplifierRewrite
  , coDoSimplifierKnownCon
  , coInlineConstants
  , coInlineFix
  , coInlineHints
  , coInlineCallsiteGrowth
  , coProfile
  , coRelaxedFloatin
  , coCaseOfCaseConservative
  , coPreserveLogging
  , coDatatypes
  , dcoStyle
  , DatatypeStyle (..)
  , defaultCompilationOpts
  , CompilationCtx
  , ccOpts
  , ccEnclosing
  , ccTypeCheckConfig
  , ccBuiltinsInfo
  , ccBuiltinCostModel
  , PirTCConfig (..)
  , AllowEscape (..)
  , toDefaultCompilationCtx
  , runCompilerPass
  , simplifier
  ) where

import Control.Lens
import Control.Monad
import Control.Monad.Except
import Control.Monad.Extra (orM, whenM)
import Data.Monoid
import Data.Monoid.Extra (mwhen)
import Debug.Trace (traceM)
import PlutusCore qualified as PLC
import PlutusIR
import PlutusIR.Compiler.Let qualified as Let
import PlutusIR.Compiler.Lower
import PlutusIR.Compiler.Provenance
import PlutusIR.Compiler.Types
import PlutusIR.Error
import PlutusIR.Pass qualified as P
import PlutusIR.Transform.Beta qualified as Beta
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

isVerbose :: Compiling m uni fun a => m Bool
isVerbose = view $ ccOpts . coVerbose

isDebug :: Compiling m uni fun a => m Bool
isDebug = view $ ccOpts . coDebug

logVerbose :: Compiling m uni fun a => String -> m ()
logVerbose = whenM (orM [isVerbose, isDebug]) . traceM

logDebug :: Compiling m uni fun a => String -> m ()
logDebug = whenM isDebug . traceM

runCompilerPass :: (Compiling m uni fun a, b ~ Provenance a) => m (P.Pass m tyname name uni fun b) -> Term tyname name uni fun b -> m (Term tyname name uni fun b)
runCompilerPass mpasses t = do
  passes <- mpasses
  pedantic <- view (ccOpts . coPedantic)
  res <- runExceptT $ P.runPass logVerbose pedantic passes t
  liftEither res

floatOutPasses :: Compiling m uni fun a => m (P.Pass m TyName Name uni fun (Provenance a))
floatOutPasses = do
  optimize <- view (ccOpts . coOptimize)
  tcconfig <- view ccTypeCheckConfig
  binfo <- view ccBuiltinsInfo
  pure $
    mwhen optimize $
      P.NamedPass "float-out" $
        fold
          [ LetFloatOut.floatTermPassSC tcconfig binfo
          , RecSplit.recSplitPass tcconfig
          , LetMerge.letMergePass tcconfig
          ]

floatInPasses :: Compiling m uni fun a => m (P.Pass m TyName Name uni fun (Provenance a))
floatInPasses = do
  optimize <- view (ccOpts . coOptimize)
  tcconfig <- view ccTypeCheckConfig
  binfo <- view ccBuiltinsInfo
  relaxed <- view (ccOpts . coRelaxedFloatin)
  pure $
    mwhen optimize $
      P.NamedPass "float-in" $
        fold
          [ LetFloatIn.floatTermPassSC tcconfig binfo relaxed
          , LetMerge.letMergePass tcconfig
          ]

simplifierIteration :: Compiling m uni fun a => String -> m (P.Pass m TyName Name uni fun (Provenance a))
simplifierIteration suffix = do
  opts <- view ccOpts
  tcconfig <- view ccTypeCheckConfig
  binfo <- view ccBuiltinsInfo
  costModel <- view ccBuiltinCostModel
  hints <- view (ccOpts . coInlineHints)
  preserveLogging <- view (ccOpts . coPreserveLogging)
  rules <- view ccRewriteRules
  ic <- view (ccOpts . coInlineConstants)
  thresh <- view (ccOpts . coInlineCallsiteGrowth)

  pure $
    P.NamedPass ("simplifier" ++ suffix) $
      fold
        [ mwhen (opts ^. coDoSimplifierUnwrapCancel) $ Unwrap.unwrapCancelPass tcconfig
        , mwhen (opts ^. coDoSimplifierCaseReduce) $ CaseReduce.caseReducePass tcconfig
        , mwhen (opts ^. coDoSimplifierKnownCon) $ KnownCon.knownConPassSC tcconfig
        , mwhen (opts ^. coDoSimplifierBeta) $ Beta.betaPassSC tcconfig
        , mwhen (opts ^. coDoSimplifierStrictifyBindings) $ StrictifyBindings.strictifyBindingsPass tcconfig binfo
        , mwhen (opts ^. coDoSimplifierEvaluateBuiltins) $ EvaluateBuiltins.evaluateBuiltinsPass tcconfig preserveLogging binfo costModel
        , mwhen (opts ^. coDoSimplifierInline) $ Inline.inlinePassSC thresh ic tcconfig hints binfo
        , mwhen (opts ^. coDoSimplifierRewrite) $ RewriteRules.rewritePassSC tcconfig rules
        ]

simplifier :: Compiling m uni fun a => m (P.Pass m TyName Name uni fun (Provenance a))
simplifier = do
  optimize <- view (ccOpts . coOptimize)
  maxIterations <- view (ccOpts . coMaxSimplifierIterations)
  passes <- for [1 .. maxIterations] $ \i -> simplifierIteration (" (pass " ++ show i ++ ")")
  pure $ mwhen optimize $ P.NamedPass "simplifier" (fold passes)

-- | Typecheck a PIR Term iff the context demands it.
typeCheckTerm :: Compiling m uni fun a => m (P.Pass m TyName Name uni fun (Provenance a))
typeCheckTerm = do
  doTc <- view (ccOpts . coTypecheck)
  tcconfig <- view ccTypeCheckConfig
  pure $ mwhen doTc $ P.typecheckPass tcconfig

dce :: Compiling m uni fun a => m (P.Pass m TyName Name uni fun (Provenance a))
dce = do
  opts <- view ccOpts
  typeCheckConfig <- view ccTypeCheckConfig
  builtinsInfo <- view ccBuiltinsInfo
  pure $
    mwhen (opts ^. coDoSimplifierRemoveDeadBindings) $
      DeadCode.removeDeadBindingsPassSC typeCheckConfig builtinsInfo

{-| The 1st half of the PIR compiler pipeline up to floating/merging the lets.
We stop momentarily here to give a chance to the tx-plugin
to dump a "readable" version of pir (i.e. floated). -}
compileToReadable
  :: forall m uni fun a b
   . (Compiling m uni fun a, b ~ Provenance a)
  => Program TyName Name uni fun b
  -> m (Program TyName Name uni fun b)
compileToReadable (Program a v t) = do
  validateOpts v
  let pipeline :: m (P.Pass m TyName Name uni fun b)
      pipeline = ala Ap foldMap [typeCheckTerm, dce, simplifier, floatOutPasses]
  Program a v <$> runCompilerPass pipeline t

{-| The 2nd half of the PIR compiler pipeline.
Compiles a 'Term' into a PLC Term, by removing/translating step-by-step the PIR's language constructs to PLC.
Note: the result *does* have globally unique names. -}
compileReadableToPlc :: forall m uni fun a b. (Compiling m uni fun a, b ~ Provenance a) => Program TyName Name uni fun b -> m (PLCProgram uni fun a)
compileReadableToPlc (Program a v t) = do
  let
    pipeline :: m (P.Pass m TyName Name uni fun b)
    pipeline =
      ala
        Ap
        foldMap
        [ floatInPasses
        , NonStrict.compileNonStrictBindingsPassSC <$> view ccTypeCheckConfig <*> pure False
        , ThunkRec.thunkRecursionsPass <$> view ccTypeCheckConfig <*> view ccBuiltinsInfo
        , -- Process only the non-strict bindings created by 'thunkRecursions' with unit delay/forces
          -- See Note [Using unit versus force/delay]
          NonStrict.compileNonStrictBindingsPassSC <$> view ccTypeCheckConfig <*> pure True
        , Let.compileLetsPassSC <$> view ccTypeCheckConfig <*> pure Let.DataTypes
        , Let.compileLetsPassSC <$> view ccTypeCheckConfig <*> pure Let.RecTerms
        , -- We introduce some non-recursive let bindings while eliminating recursive let-bindings,
          -- so we can eliminate any of them which are unused here.
          dce
        , simplifier
        , Let.compileLetsPassSC <$> view ccTypeCheckConfig <*> pure Let.Types
        , Let.compileLetsPassSC <$> view ccTypeCheckConfig <*> pure Let.NonRecTerms
        ]

    go =
      runCompilerPass pipeline
        >=> (<$ logVerbose "  !!! lowerTerm")
        >=> lowerTerm

  PLC.Program a v <$> go t

--- | Compile a 'Program' into a PLC Program. Note: the result *does* have globally unique names.
compileProgram
  :: Compiling m uni fun a
  => Program TyName Name uni fun a -> m (PLCProgram uni fun a)
compileProgram =
  (pure . original)
    >=> (<$ logDebug "!!! compileToReadable")
    >=> compileToReadable
    >=> (<$ logDebug "!!! compileReadableToPlc")
    >=> compileReadableToPlc
