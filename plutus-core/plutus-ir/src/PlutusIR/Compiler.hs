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
    coPedantic,
    coVerbose,
    coDebug,
    coDumpCert,
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
    simplifyTerm
    ) where

import PlutusIR

import PlutusIR.Compiler.Let qualified as Let
import PlutusIR.Compiler.Lower
import PlutusIR.Compiler.Provenance
import PlutusIR.Compiler.Types
import PlutusIR.Error
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
import PlutusIR.TypeCheck.Internal

import PlutusCore qualified as PLC

import Control.Lens
import Control.Monad
import Control.Monad.Extra (orM, whenM)
import Control.Monad.Reader
import Control.Monad.State
import Debug.Trace (traceM)
import PlutusIR.Analysis.Builtins
import PlutusPrelude

-- Simplifier passes
data Pass uni fun =
  Pass { _name      :: String
       , _shouldRun :: forall m e a. Compiling m e uni fun a => m Bool
       , _pass      :: forall m e a. Compiling m e uni fun a => Term TyName Name uni fun (Provenance a) -> m (Term TyName Name uni fun (Provenance a))
       }

onOption :: Compiling m e uni fun a => Lens' (CompilationOpts a) Bool -> m Bool
onOption coOpt = view (ccOpts . coOpt)

isVerbose :: Compiling m e uni fun a => m Bool
isVerbose = view $ ccOpts . coVerbose

isDebug :: Compiling m e uni fun a => m Bool
isDebug = view $ ccOpts . coDebug

isCert :: Compiling m e uni fun a => m Bool
isCert = view $ ccOpts . coDumpCert

logVerbose :: Compiling m e uni fun a => String -> m ()
logVerbose = whenM (orM [isVerbose, isDebug]) . traceM

logDebug :: Compiling m e uni fun a => String -> m ()
logDebug = whenM isDebug . traceM

updateCertTrace :: Compiling m e uni fun a => PassMeta -> Term TyName Name uni fun (Provenance a) -> m (Term TyName Name uni fun (Provenance a))
updateCertTrace pm t = t <$ whenM isCert (modify addPass)
  where
    addPass (CompilationTrace t0 ps) = CompilationTrace t0 (ps ++ [(pm, void t)])

applyPass :: (Compiling m e uni fun a, b ~ Provenance a) => Pass uni fun -> Term TyName Name uni fun b -> m (Term TyName Name uni fun b)
applyPass pass = runIf (_shouldRun pass) $ through check <=< \term -> do
  let passName = _name pass
  logVerbose $ "      !!! " ++ passName
  logDebug   $ "        !!! Before " ++ passName ++ "\n" ++ show (pretty term)
  term' <- _pass pass term
  logDebug   $ "        !!! After " ++ passName ++ "\n" ++ show (pretty term')
  pure term'

availablePasses :: [Pass uni fun]
availablePasses =
    [ Pass "unwrap cancel"        (onOption coDoSimplifierUnwrapCancel)       (\t -> do
                                                                                  let t' = Unwrap.unwrapCancel t
                                                                                  updateCertTrace PassUnwrapWrap t')
    , Pass "case reduce"          (onOption coDoSimplifierCaseReduce)         (\t -> do
                                                                                  let t' = CaseReduce.caseReduce t
                                                                                  updateCertTrace PassCaseReduce t')
    , Pass "case of case"         (onOption coDoSimplifierCaseOfCase)         (\t -> do
                                                                                  binfo <- view ccBuiltinsInfo
                                                                                  conservative <- view (ccOpts . coCaseOfCaseConservative)

                                                                                  -- We are going to record information about variables in a global map, so we
                                                                                  -- need global uniqueness
                                                                                  ( PLC.rename
                                                                                    >=> CaseOfCase.caseOfCase binfo conservative noProvenance
                                                                                    >=> updateCertTrace PassCaseOfCase) t
                                                                              )
    , Pass "known constructor"    (onOption coDoSimplifierKnownCon)           (\t -> do
                                                                                  t' <- KnownCon.knownCon t
                                                                                  updateCertTrace PassKnownConstructor t'
                                                                              )
    , Pass "beta"                 (onOption coDoSimplifierBeta)               (\t -> do
                                                                                  let t' = Beta.beta t
                                                                                  updateCertTrace PassBeta t'
                                                                              )
    , Pass "strictify bindings"   (onOption coDoSimplifierStrictifyBindings)  (\t -> do
                                                                                  binfo <- view ccBuiltinsInfo
                                                                                  let t' = StrictifyBindings.strictifyBindings binfo t
                                                                                  updateCertTrace PassStrictifyBindings t'
                                                                              )
    , Pass "evaluate builtins"    (onOption coDoSimplifierEvaluateBuiltins)   (\t -> do
                                                                                  binfo <- view ccBuiltinsInfo
                                                                                  costModel <- view ccBuiltinCostModel
                                                                                  preserveLogging <- view (ccOpts . coPreserveLogging)
                                                                                  let t' = EvaluateBuiltins.evaluateBuiltins preserveLogging binfo costModel t
                                                                                  updateCertTrace PassEvaluateBuiltins t'
                                                                              )
    , Pass "inline"               (onOption coDoSimplifierInline)             (\t -> do
                                                                                  hints <- view (ccOpts . coInlineHints)
                                                                                  binfo <- view ccBuiltinsInfo
                                                                                  trackElims <- view (ccOpts . coDumpCert)
                                                                                  (t', (elim, elimsTy)) <- Inline.inline hints binfo trackElims t
                                                                                  updateCertTrace (PassInline elim elimsTy) t'
                                                                              )
    , Pass "rewrite rules" (onOption coDoSimplifierRewrite) (\ t -> do
                                                                    rules <- view ccRewriteRules
                                                                    t' <- RewriteRules.rewriteWith rules t
                                                                    updateCertTrace PassRewriteRules t'
                                                                    )
    ]

-- | Actual simplifier
simplify
    :: forall m e uni fun a b. (Compiling m e uni fun a, b ~ Provenance a)
    => Term TyName Name uni fun b -> m (Term TyName Name uni fun b)
simplify = foldl' (>=>) pure (map applyPass availablePasses)

-- | Perform some simplification of a 'Term'.
--
-- NOTE: simplifyTerm requires at least 1 prior dead code elimination pass
simplifyTerm
  :: forall m e uni fun a b. (Compiling m e uni fun a, b ~ Provenance a)
  => Term TyName Name uni fun b -> m (Term TyName Name uni fun b)
simplifyTerm = runIfOpts simplify'
    where
        simplify' :: Term TyName Name uni fun b -> m (Term TyName Name uni fun b)
        simplify' t = do
            maxIterations <- view (ccOpts . coMaxSimplifierIterations)
            simplifyNTimes maxIterations t
        -- Run the simplifier @n@ times
        simplifyNTimes :: Int -> Term TyName Name uni fun b -> m (Term TyName Name uni fun b)
        simplifyNTimes n = foldl' (>=>) pure (map simplifyStep [1 .. n])
        -- generate simplification step
        simplifyStep :: Int -> Term TyName Name uni fun b -> m (Term TyName Name uni fun b)
        simplifyStep i term = do
          logVerbose $ "    !!! simplifier pass " ++ show i
          simplify term


-- | Perform floating out/merging of lets in a 'Term' to their
-- nearest lambda/Lambda/letStrictNonValue.
-- Note: It assumes globally unique names
floatOut
    :: (Compiling m e uni fun a, Semigroup b, b ~ Provenance a)
    => Term TyName Name uni fun b
    -> m (Term TyName Name uni fun b)
floatOut t = do
    binfo <- view ccBuiltinsInfo
    flip runIfOpts t $ do
      pure . LetFloatOut.floatTerm binfo
      >=> updateCertTrace PassFloatOut
      >=> pure . RecSplit.recSplit
      >=> updateCertTrace PassRecSplit
      >=> pure . LetMerge.letMerge
      >=> updateCertTrace PassLetMerge

-- | Perform floating in/merging of lets in a 'Term'.
floatIn
    :: (Compiling m e uni fun a, b ~ Provenance a)
    => Term TyName Name uni fun b
    -> m (Term TyName Name uni fun b)
floatIn t = do
    binfo <- view ccBuiltinsInfo
    relaxed <- view (ccOpts . coRelaxedFloatin)
    flip runIfOpts t $ do
      PLC.rename
      >=> updateCertTrace PassRename
      >=> LetFloatIn.floatTerm binfo relaxed
      >=> updateCertTrace PassFloatIn
      >=> pure . LetMerge.letMerge
      >=> updateCertTrace PassLetMerge

deadCode
    :: (Compiling m e uni fun a, b ~ Provenance a)
    => Term TyName Name uni fun b
    -> m (Term TyName Name uni fun b)
deadCode =
  PLC.rename
  >=> updateCertTrace PassRename
  >=> withBuiltinsInfo . flip DeadCode.removeDeadBindings
  >=> updateCertTrace PassDeadCode

-- | Typecheck a PIR Term iff the context demands it.
-- Note: assumes globally unique names
typeCheckTerm :: (Compiling m e uni fun a, b ~ Provenance a) => Term TyName Name uni fun b -> m ()
typeCheckTerm t = do
    mtcconfig <- asks _ccTypeCheckConfig
    case mtcconfig of
        Just tcconfig -> void . runTypeCheckM tcconfig $ inferTypeM t
        Nothing       -> pure ()

check :: Compiling m e uni fun b => Term TyName Name uni fun (Provenance b) -> m ()
check arg =
    whenM (view (ccOpts . coPedantic)) $
         -- the typechecker requires global uniqueness, so rename here
        typeCheckTerm =<< PLC.rename arg

withBuiltinsInfo
    :: MonadReader (CompilationCtx uni fun a) m
    => (BuiltinsInfo uni fun -> m t)
    -> m t
withBuiltinsInfo = (view ccBuiltinsInfo >>=)

-- | The 1st half of the PIR compiler pipeline up to floating/merging the lets.
-- We stop momentarily here to give a chance to the tx-plugin
-- to dump a "readable" version of pir (i.e. floated).
compileToReadable
  :: (Compiling m e uni fun a, b ~ Provenance a)
  => Program TyName Name uni fun b
  -> m (Program TyName Name uni fun b)
compileToReadable (Program a v t) =
  let pipeline =
        -- We need globally unique names for typechecking, floating, and compiling non-strict bindings
        (<$ logVerbose "  !!! rename")
        >=> PLC.rename
        >=> updateCertTrace PassRename
        >=> through typeCheckTerm
        >=> (<$ logVerbose "  !!! removeDeadBindings")
        >=> deadCode
        >=> (<$ logVerbose "  !!! simplifyTerm")
        >=> simplifyTerm
        >=> (<$ logVerbose "  !!! floatOut")
        >=> floatOut
        >=> through check
  in validateOpts v >> Program a v <$> pipeline t

-- | The 2nd half of the PIR compiler pipeline.
-- Compiles a 'Term' into a PLC Term, by removing/translating step-by-step the PIR's language constructs to PLC.
-- Note: the result *does* have globally unique names.
compileReadableToPlc :: (Compiling m e uni fun a, b ~ Provenance a) => Program TyName Name uni fun b -> m (PLCProgram uni fun a)
compileReadableToPlc (Program a v t) =
  let pipeline =
        (<$ logVerbose "  !!! floatIn")
        >=> floatIn
        >=> through check
        >=> (<$ logVerbose "  !!! compileNonStrictBindings")
        >=> NonStrict.compileNonStrictBindings False
        >=> updateCertTrace PassCompileLetNonStrict
        >=> through check
        >=> (<$ logVerbose "  !!! thunkRecursions")
        >=> (withBuiltinsInfo . fmap pure . flip ThunkRec.thunkRecursions)
        >=> updateCertTrace PassThunkRec
        -- Thunking recursions breaks global uniqueness
        >=> PLC.rename
        >=> updateCertTrace PassRename
        >=> through check
        -- Process only the non-strict bindings created by 'thunkRecursions' with unit delay/forces
        -- See Note [Using unit versus force/delay]
        >=> (<$ logVerbose "  !!! compileNonStrictBindings")
        >=> NonStrict.compileNonStrictBindings True
        >=> updateCertTrace PassCompileLetNonStrict
        >=> through check
        >=> (<$ logVerbose "  !!! compileLets DataTypes")
        >=> Let.compileLets Let.DataTypes
        >=> updateCertTrace PassCompileLetData
        >=> through check
        >=> (<$ logVerbose "  !!! compileLets RecTerms")
        >=> Let.compileLets Let.RecTerms
        >=> updateCertTrace PassCompileLetRec
        >=> through check
        -- We introduce some non-recursive let bindings while eliminating recursive let-bindings, so we
        -- can eliminate any of them which are unused here.
        >=> (<$ logVerbose "  !!! removeDeadBindings")
        >=> deadCode
        >=> through check
        >=> (<$ logVerbose "  !!! simplifyTerm")
        >=> simplifyTerm
        >=> through check
        >=> (<$ logVerbose "  !!! compileLets Types")
        >=> Let.compileLets Let.Types
        >=> updateCertTrace PassCompileLetType
        >=> through check
        >=> (<$ logVerbose "  !!! compileLets NonRecTerms")
        >=> Let.compileLets Let.NonRecTerms
        >=> updateCertTrace PassCompileLetNonRec
        >=> through check
        >=> (<$ logVerbose "  !!! lowerTerm")
        >=> lowerTerm
  in PLC.Program a v <$> pipeline t

--- | Compile a 'Program' into a PLC Program. Note: the result *does* have globally unique names.
compileProgram :: Compiling m e uni fun a
            => Program TyName Name uni fun a -> m (PLCProgram uni fun a)
compileProgram =
  (pure . original)
  >=> (<$ logVerbose "!!! compileToReadable")
  >=> compileToReadable
  >=> (<$ logVerbose "!!! compileReadableToPlc")
  >=> compileReadableToPlc

