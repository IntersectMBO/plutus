-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskellQuotes      #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}
-- For some reason this module is very slow to compile otherwise
{-# OPTIONS_GHC -O0 #-}
module PlutusTx.Plugin (plugin, plc) where

import Data.Bifunctor
import PlutusPrelude
import PlutusTx.Code
import PlutusTx.Compiler.Builtins
import PlutusTx.Compiler.Error
import PlutusTx.Compiler.Expr
import PlutusTx.Compiler.Types
import PlutusTx.Compiler.Utils
import PlutusTx.Coverage
import PlutusTx.PIRTypes
import PlutusTx.PLCTypes
import PlutusTx.Plugin.Utils
import PlutusTx.Trace

import GHC.ByteCode.Types qualified as GHC
import GHC.Core.FamInstEnv qualified as GHC
import GHC.Core.Opt.OccurAnal qualified as GHC
import GHC.Core.Unfold qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Types.TyThing qualified as GHC
import GHC.Utils.Logger qualified as GHC

import PlutusCore qualified as PLC
import PlutusCore.Compiler qualified as PLC
import PlutusCore.Pretty as PLC
import PlutusCore.Quote

import UntypedPlutusCore qualified as UPLC

import PlutusIR qualified as PIR
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Compiler.Definitions qualified as PIR
import PlutusTx.Options

import Language.Haskell.TH.Syntax as TH hiding (lift)

import Control.Exception (throwIO)
import Control.Lens
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer hiding (All)
import Flat (Flat, flat, unflat)

import Data.ByteString qualified as BS
import Data.ByteString.Unsafe qualified as BSUnsafe
import Data.Either.Validation
import Data.Map qualified as Map
import Data.Set qualified as Set
import Prettyprinter qualified as PP
import System.IO (openTempFile)
import System.IO.Unsafe (unsafePerformIO)

data PluginCtx = PluginCtx
    { pcOpts            :: PluginOptions
    , pcFamEnvs         :: GHC.FamInstEnvs
    , pcMarkerName      :: GHC.Name
    , pcModuleName      :: GHC.ModuleName
    , pcModuleModBreaks :: Maybe GHC.ModBreaks
    }

{- Note [Making sure unfoldings are present]
Our plugin runs at the start of the Core pipeline. If we look around us, we will find
that as expected, we have unfoldings for some bindings from other modules or packages
depending on whether GHC thinks they're good to inline/are marked INLINEABLE.

But there will be no unfoldings for local bindings!

It turns out that these are added by the simplifier, of all things. To avoid relying too
much on the shape of the subsequent passes, we add a single, very gentle, simplifier
pass before we run, turning off everything that we can and running only once.

This means that we need to be robust to the transformations that the simplifier performs
unconditionally which we pretty much are.

See https://gitlab.haskell.org/ghc/ghc/issues/16615 for upstream discussion.
-}

{- Note [newtype field accessors in `base`]
For some unknown reason, newtype field accessors in `base`, such as `getFirst`, `appEndo` and
`getDual`, cause Cabal build and Nix build to behave differently. In Cabal build, these
field accessors' unfoldings are available to the GHC simplifier, and so the simplifier inlines
them into `Coercion`s. But in Nix build, somehow their unfoldings aren't available.

This started to happen after a seemingly innocent PR (#4552), and it eventually led to different
PIRs, PLCs and UPLCs, causing test failures. Replacing them with `coerce` avoids the problem.
-}

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin { GHC.pluginRecompile = GHC.flagRecompile
                           , GHC.installCoreToDos = install
                           }
    where
      install :: [GHC.CommandLineOption] -> [GHC.CoreToDo] -> GHC.CoreM [GHC.CoreToDo]
      install args rest = do
          -- create simplifier pass to be placed at the front
          simplPass <- mkSimplPass <$> GHC.getDynFlags <*> GHC.getLogger
          -- instantiate our plugin pass
          pluginPass <- mkPluginPass <$> case parsePluginOptions args of
              Success opts -> pure opts
              Failure errs -> liftIO $ throwIO errs
          -- return the pipeline
          pure $
             simplPass
             : pluginPass
             : rest

{- Note [GHC.sm_pre_inline]
We run a GHC simplifier pass before the plugin, in which we turn on `sm_pre_inline`, which
makes GHC inline certain bindings before the plugin runs. Pre-inlining is a phase of the GHC
inliner that inlines bindings in GHC Core where the binder occurs exactly once in an
unconditionally safe way (e.g., the occurrence isn't inside a lambda). For details, see paper
"Secrets of the Glasgow Haskell Compiler inliner".

The reason we need the pre-inlining is that the plugin requires certain functions
to be fully applied. For example, it has a special rule to handle
`noinline @(String -> BuiltinString) stringToBuiltinString "a"`, but it cannot compile
`let f = noinline @(String -> BuiltinString) stringToBuiltinString in f "a"`.
By turning on pre-inlining, the `f` in the latter expression will be inlined, resulting in
the former expression, which the plugin knows how to compile.

There is a related flag, `sm_inline`, which controls whether GHC's call-site inlining is
enabled. If enabled, GHC will inline additional bindings that cannot be unconditionally
inlined, on a call-site-by-call-site basis. Currently we haven't found the need to turn on
`sm_inline`. Turning it on seems to reduce PIR sizes in many cases, but it is unclear
whether it may affect the semantics of Plutus Core.

Arguably, relying on `sm_pre_inline` is not the proper solution - what if we get
`let f = noinline @(String -> BuiltinString) stringToBuiltinString in f "a" <> f "b"`?
Here `f` won't be pre-inlined because it occurs twice. Instead, we should perhaps
inline a binding when the RHS is a partially applied function that we need fully applied.
But so far we haven't had an issue like this.

We should also make the error message better in cases like this. The current error message is
"Unsupported feature: Type constructor: GHC.Prim.Char#", resulting from attempting to inline
and compile `stringToBuiltinString`.
-}

-- | A simplifier pass, implemented by GHC
mkSimplPass :: GHC.DynFlags -> GHC.Logger -> GHC.CoreToDo
mkSimplPass flags logger =
  -- See Note [Making sure unfoldings are present]
  GHC.CoreDoSimplify 1 $ GHC.SimplMode {
              GHC.sm_names = ["Ensure unfoldings are present"]
            , GHC.sm_phase = GHC.InitialPhase
            , GHC.sm_uf_opts = GHC.defaultUnfoldingOpts
            , GHC.sm_dflags = flags
            , GHC.sm_rules = False
            , GHC.sm_cast_swizzle = True
            -- See Note [GHC.sm_pre_inline]
            , GHC.sm_pre_inline = True
            , GHC.sm_logger = logger
            -- You might think you would need this, but apparently not
            , GHC.sm_inline = False
            , GHC.sm_case_case = False
            , GHC.sm_eta_expand = False
            }

{- Note [Marker resolution]
We use TH's 'foo exact syntax for resolving the 'plc marker's ghc name, as
explained in: <http://hackage.haskell.org/package/ghc-8.10.1/docs/GhcPlugins.html#v:thNameToGhcName>

The GHC haddock suggests that the "exact syntax" will always succeed because it is statically resolved here (inside this Plugin module);

If this is the case, then it means that our plugin will always traverse each module's binds searching for plc markers
even in the case that the `plc` name is not in scope locally in the module under compilation.

The alternative is to use the "dynamic syntax" (`TH.mkName "plc"`), which implies that
the "plc" name will be resolved dynamically during module's compilation. In case "plc" is not locally in scope,
the plugin would finish faster by completely skipping the module under compilation. This dynamic approach
comes with its own downsides however, because the user may have imported "plc" qualified or aliased it, which will fail to resolve.
-}


-- | Our plugin works at haskell-module level granularity; the plugin
-- looks at the module's top-level bindings for plc markers and compiles their right-hand-side core expressions.
mkPluginPass :: PluginOptions -> GHC.CoreToDo
mkPluginPass opts = GHC.CoreDoPluginPass "Core to PLC" $ \ guts -> do
    -- Family env code borrowed from SimplCore
    p_fam_env <- GHC.getPackageFamInstEnv
    -- See Note [Marker resolution]
    maybeMarkerName <- GHC.thNameToGhcName 'plc
    case maybeMarkerName of
        -- TODO: test that this branch can happen using TH's 'plc exact syntax. See Note [Marker resolution]
        Nothing -> pure guts
        Just markerName ->
            let pctx = PluginCtx { pcOpts = opts
                                 , pcFamEnvs = (p_fam_env, GHC.mg_fam_inst_env guts)
                                 , pcMarkerName = markerName
                                 , pcModuleName = GHC.moduleName $ GHC.mg_module guts
                                 , pcModuleModBreaks = GHC.mg_modBreaks guts
                                 }
                -- start looking for plc calls from the top-level binds
            in GHC.bindsOnlyPass (runPluginM pctx . traverse compileBind) guts

-- | The monad where the plugin runs in for each module.
-- It is a core->core compiler monad, called PluginM, augmented with pure errors.
type PluginM uni fun = ReaderT PluginCtx (ExceptT (CompileError uni fun Ann) GHC.CoreM)

-- | Runs the plugin monad in a given context; throws a Ghc.Exception when compilation fails.
runPluginM :: (PLC.Pretty (PLC.SomeTypeIn uni), PLC.Closed uni, PLC.Everywhere uni PLC.PrettyConst, PP.Pretty fun)
           => PluginCtx -> PluginM uni fun a -> GHC.CoreM a
runPluginM pctx act = do
    res <- runExceptT $ runReaderT act pctx
    case res of
        Right x -> pure x
        Left err ->
            let errInGhc = GHC.ProgramError . show $ "GHC Core to PLC plugin:" PP.<+> PP.pretty err
            in liftIO $ GHC.throwGhcExceptionIO errInGhc

-- | Compiles all the marked expressions in the given binder into PLC literals.
compileBind :: GHC.CoreBind -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreBind
compileBind = \case
    GHC.NonRec b rhs -> GHC.NonRec b <$> compileMarkedExprs rhs
    GHC.Rec bindsRhses -> GHC.Rec <$> (for bindsRhses $ \(b, rhs) -> do
                                             rhs' <- compileMarkedExprs rhs
                                             pure (b, rhs'))

{- Note [Hooking in the plugin]
Working out what to process and where to put it is tricky. We are going to turn the result in
to a 'CompiledCode', not the Haskell expression we started with!

Currently we look for calls to the @plc :: a -> CompiledCode a@ function, and we replace the whole application with the
generated code object, which will still be well-typed.
-}

{- Note [Polymorphic values and Any]
If you try and use the plugin on a polymorphic expression, then GHC will replace the quantified types
with 'Any' and remove the type lambdas. This is pretty annoying, and I don't entirely understand
why it happens, despite poking around in GHC a fair bit.

Possibly it has to do with the type that is given to 'plc' being unconstrained, resulting in GHC
putting 'Any' there, and that then propagating into the type of the quote. It's tricky to experiment
with this, since you can't really specify a polymorphic type in a type application or in the resulting
'CompiledCode' because that's impredicative polymorphism.
-}

-- | Compiles all the core-expressions surrounded by plc in the given expression into PLC literals.
compileMarkedExprs :: GHC.CoreExpr -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreExpr
compileMarkedExprs expr = do
    markerName <- asks pcMarkerName
    case expr of
      GHC.App (GHC.App (GHC.App (GHC.App
                          -- function id
                          -- sometimes GHCi sticks ticks around this for some reason
                          (stripTicks -> (GHC.Var fid))
                          -- first type argument, must be a string literal type
                          (GHC.Type (GHC.isStrLitTy -> Just fs_locStr)))
                     -- second type argument
                     (GHC.Type codeTy))
            _)
            -- value argument
            inner
          | markerName == GHC.idName fid -> compileMarkedExprOrDefer (show fs_locStr) codeTy inner
      e@(GHC.Var fid) | markerName == GHC.idName fid -> throwError . NoContext . InvalidMarkerError . GHC.showSDocUnsafe $ GHC.ppr e
      GHC.App e a -> GHC.App <$> compileMarkedExprs e <*> compileMarkedExprs a
      GHC.Lam b e -> GHC.Lam b <$> compileMarkedExprs e
      GHC.Let bnd e -> GHC.Let <$> compileBind bnd <*> compileMarkedExprs e
      GHC.Case e b t alts -> do
            e' <- compileMarkedExprs e
            let expAlt (GHC.Alt a bs rhs) = GHC.Alt a bs <$> compileMarkedExprs rhs
            alts' <- mapM expAlt alts
            pure $ GHC.Case e' b t alts'
      GHC.Cast e c -> flip GHC.Cast c <$> compileMarkedExprs e
      GHC.Tick t e -> GHC.Tick t <$> compileMarkedExprs e
      e@(GHC.Coercion _) -> pure e
      e@(GHC.Lit _) -> pure e
      e@(GHC.Var _) -> pure e
      e@(GHC.Type _) -> pure e

-- | Behaves the same as 'compileMarkedExpr', unless a compilation error occurs ;
-- if a compilation error happens and the 'defer-errors' option is turned on,
-- the compilation error is suppressed and the original hs expression is replaced with a
-- haskell runtime-error expression.
compileMarkedExprOrDefer :: String -> GHC.Type -> GHC.CoreExpr -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreExpr
compileMarkedExprOrDefer locStr codeTy origE = do
    opts <- asks pcOpts
    let compileAct = compileMarkedExpr locStr codeTy origE
    if _posDeferErrors opts
      -- TODO: we could perhaps move this catchError to the "runExceptT" module-level, but
      -- it leads to uglier code and difficulty of handling other pure errors
      then compileAct `catchError` emitRuntimeError codeTy
      else compileAct

-- | Given an expected Haskell type 'a', it generates Haskell code which throws a GHC runtime error "as" 'CompiledCode a'.
emitRuntimeError :: (PLC.Pretty (PLC.SomeTypeIn uni), PLC.Closed uni, PP.Pretty fun, PLC.Everywhere uni PLC.PrettyConst)
                 => GHC.Type -> CompileError uni fun Ann -> PluginM uni fun GHC.CoreExpr
emitRuntimeError codeTy e = do
    opts <- asks pcOpts
    let shown = show $ PP.pretty (pruneContext (_posContextLevel opts) e)
    tcName <- thNameToGhcNameOrFail ''CompiledCode
    tc <- lift . lift $ GHC.lookupTyCon tcName
    pure $ GHC.mkRuntimeErrorApp GHC.rUNTIME_ERROR_ID (GHC.mkTyConApp tc [codeTy]) shown

-- | Compile the core expression that is surrounded by a 'plc' marker,
-- and return a core expression which evaluates to the compiled plc AST as a serialized bytestring,
-- to be injected back to the Haskell program.
compileMarkedExpr :: String -> GHC.Type -> GHC.CoreExpr -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreExpr
compileMarkedExpr locStr codeTy origE = do
    flags <- GHC.getDynFlags
    famEnvs <- asks pcFamEnvs
    opts <- asks pcOpts
    moduleName <- asks pcModuleName
    let moduleNameStr = GHC.showSDocForUser flags GHC.emptyUnitState GHC.alwaysQualify (GHC.ppr moduleName)
    -- We need to do this out here, since it has to run in CoreM
    nameInfo <- makePrimitiveNameInfo $ builtinNames ++ [''Bool, 'False, 'True, 'traceBool]
    modBreaks <- asks pcModuleModBreaks
    let coverage = CoverageOpts . Set.fromList $
                   [ l | _posCoverageAll opts, l <- [minBound .. maxBound]]
                ++ [ LocationCoverage  | _posCoverageLocation opts  ]
                ++ [ BooleanCoverage  | _posCoverageBoolean opts  ]
    let ctx = CompileContext {
            ccOpts = CompileOptions {coProfile=_posProfile opts,coCoverage=coverage,coRemoveTrace=_posRemoveTrace opts},
            ccFlags = flags,
            ccFamInstEnvs = famEnvs,
            ccNameInfo = nameInfo,
            ccScopes = initialScopeStack,
            ccBlackholed = mempty,
            ccCurDef = Nothing,
            ccModBreaks = modBreaks,
            ccBuiltinVer = def
            }
    -- See Note [Occurrence analysis]
    let origE' = GHC.occurAnalyseExpr origE

    ((pirP,uplcP), covIdx) <- runWriterT . runQuoteT . flip runReaderT ctx $
        withContextM 1 (sdToTxt $ "Compiling expr at" GHC.<+> GHC.text locStr) $
            runCompiler moduleNameStr opts origE'

    -- serialize the PIR, PLC, and coverageindex outputs into a bytestring.
    bsPir <- makeByteStringLiteral $ flat pirP
    bsPlc <- makeByteStringLiteral $ flat uplcP
    covIdxFlat <- makeByteStringLiteral $ flat covIdx

    builder <- lift . lift . GHC.lookupId =<< thNameToGhcNameOrFail 'mkCompiledCode

    -- inject the three bytestrings back as Haskell code.
    pure $
        GHC.Var builder
        `GHC.App` GHC.Type codeTy
        `GHC.App` bsPlc
        `GHC.App` bsPir
        `GHC.App` covIdxFlat

-- | The GHC.Core to PIR to PLC compiler pipeline. Returns both the PIR and PLC output.
-- It invokes the whole compiler chain:  Core expr -> PIR expr -> PLC expr -> UPLC expr.
runCompiler ::
    forall uni fun m.
    ( uni ~ PLC.DefaultUni
    , fun ~ PLC.DefaultFun
    , MonadReader (CompileContext uni fun) m
    , MonadWriter CoverageIndex m
    , MonadQuote m
    , MonadError (CompileError uni fun Ann) m
    , MonadIO m
    ) =>
    String ->
    PluginOptions ->
    GHC.CoreExpr ->
    m (PIRProgram uni fun, UPLCProgram uni fun)
runCompiler moduleName opts expr = do
    -- Plc configuration
    plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance

    let hints = UPLC.InlineHints $ \ann _ -> case ann of
            -- See Note [The problem of inlining destructors]
            -- We want to inline destructors, but even in UPLC our inlining heuristics
            -- aren't quite smart enough to tell that they're good inlining candidates,
            -- so we just explicitly tell the inliner to inline them all.
            --
            -- In fact, this instructs the inliner to inline *any* binding inside a destructor,
            -- which is a slightly large hammer but is actually what we want since it will mean
            -- that we also aggressively reduce the bindings inside the destructor.
            PIR.DatatypeComponent PIR.Destructor _ -> True
            _                                      -> AlwaysInline `elem` fmap annInline (toList ann)
    -- Compilation configuration
    let pirTcConfig = if _posDoTypecheck opts
                      -- pir's tc-config is based on plc tcconfig
                      then Just $ PIR.PirTCConfig plcTcConfig PIR.YesEscape
                      else Nothing
        pirCtx = PIR.toDefaultCompilationCtx plcTcConfig
                 & set (PIR.ccOpts . PIR.coOptimize) (_posOptimize opts)
                 & set (PIR.ccOpts . PIR.coPedantic) (_posPedantic opts)
                 & set (PIR.ccOpts . PIR.coVerbose) (_posVerbosity opts == Verbose)
                 & set (PIR.ccOpts . PIR.coDebug) (_posVerbosity opts == Debug)
                 & set (PIR.ccOpts . PIR.coMaxSimplifierIterations) (_posMaxSimplifierIterationsPir opts)
                 & set PIR.ccTypeCheckConfig pirTcConfig
                 -- Simplifier options
                 & set (PIR.ccOpts . PIR.coDoSimplifierUnwrapCancel)       (_posDoSimplifierUnwrapCancel opts)
                 & set (PIR.ccOpts . PIR.coDoSimplifierBeta)               (_posDoSimplifierBeta opts)
                 & set (PIR.ccOpts . PIR.coDoSimplifierInline)             (_posDoSimplifierInline opts)
                 & set (PIR.ccOpts . PIR.coInlineHints)                    hints
                 & set (PIR.ccOpts . PIR.coRelaxedFloatin) (_posRelaxedFloatin opts)
        plcOpts = PLC.defaultCompilationOpts
            & set (PLC.coSimplifyOpts . UPLC.soMaxSimplifierIterations) (_posMaxSimplifierIterationsUPlc opts)
            & set (PLC.coSimplifyOpts . UPLC.soInlineHints) hints

    -- GHC.Core -> Pir translation.
    pirT <- PIR.runDefT annMayInline $ compileExprWithDefs expr
    when (_posDumpPir opts) . liftIO $
        dumpFlat (PIR.Program () PLC.latestVersion (void pirT)) "initial PIR program" (moduleName ++ ".pir-initial.flat")

    -- Pir -> (Simplified) Pir pass. We can then dump/store a more legible PIR program.
    spirT <- flip runReaderT pirCtx $ PIR.compileToReadable pirT
    let spirPNoAnn = PIR.Program () PLC.latestVersion $ void $ spirT
        spirP = PIR.Program mempty PLC.latestVersion . fmap getSrcSpans $ spirT
    when (_posDumpPir opts) . liftIO $ dumpFlat spirPNoAnn "simplified PIR program" (moduleName ++ ".pir-simplified.flat")

    -- (Simplified) Pir -> Plc translation.
    plcT <- flip runReaderT pirCtx $ PIR.compileReadableToPlc spirT
    let plcP = PLC.Program () PLC.latestVersion $ void plcT
    when (_posDumpPlc opts) . liftIO $ dumpFlat plcP "typed PLC program" (moduleName ++ ".plc.flat")

    -- We do this after dumping the programs so that if we fail typechecking we still get the dump.
    when (_posDoTypecheck opts) . void $
        liftExcept $ PLC.inferTypeOfProgram plcTcConfig (plcP $> annMayInline)

    uplcT <- flip runReaderT plcOpts $ PLC.compileTerm plcT
    dbT <- liftExcept $ UPLC.deBruijnTerm uplcT
    let uplcPNoAnn = UPLC.Program () PLC.latestVersion $ void dbT
        uplcP = UPLC.Program mempty PLC.latestVersion . fmap getSrcSpans $ dbT
    when (_posDumpUPlc opts) . liftIO $ dumpFlat uplcPNoAnn "untyped PLC program" (moduleName ++ ".uplc.flat")
    pure (spirP, uplcP)

  where
      -- ugly trick to take out the concrete plc.error and in case of error, map it / rethrow it using our 'CompileError'
      liftExcept :: ExceptT (PLC.Error PLC.DefaultUni PLC.DefaultFun Ann) m b -> m b
      liftExcept act = do
        plcTcError <- runExceptT act
        -- also wrap the PLC Error annotations into Original provenances, to match our expected 'CompileError'
        liftEither $ first (view (re PIR._PLCError) . fmap PIR.Original) plcTcError

      dumpFlat :: Flat t => t -> String -> String -> IO ()
      dumpFlat t desc fileName = do
        (tPath, tHandle) <- openTempFile "." fileName
        putStrLn $ "!!! dumping " ++ desc ++ " to " ++ show tPath
        BS.hPut tHandle $ flat t

      getSrcSpans :: PIR.Provenance Ann -> SrcSpans
      getSrcSpans = SrcSpans . Set.unions . fmap (unSrcSpans . annSrcSpans) . toList

-- | Get the 'GHC.Name' corresponding to the given 'TH.Name', or throw an error if we can't get it.
thNameToGhcNameOrFail :: TH.Name -> PluginM uni fun GHC.Name
thNameToGhcNameOrFail name = do
    maybeName <- lift . lift $ GHC.thNameToGhcName name
    case maybeName of
        Just n  -> pure n
        Nothing -> throwError . NoContext $ CoreNameLookupError name

-- | Create a GHC Core expression that will evaluate to the given ByteString at runtime.
makeByteStringLiteral :: BS.ByteString -> PluginM uni fun GHC.CoreExpr
makeByteStringLiteral bs = do
    flags <- GHC.getDynFlags

    {-
    This entire section will crash horribly in a number of circumstances. Such is life.
    - If any of the names we need can't be found as GHC Names
    - If we then can't look up those GHC Names to get their IDs/types
    - If we make any mistakes creating the Core expression
    -}

    -- Get the names of functions/types that we need for our expression
    upio <- lift . lift . GHC.lookupId =<< thNameToGhcNameOrFail 'unsafePerformIO
    bsTc <- lift . lift . GHC.lookupTyCon =<< thNameToGhcNameOrFail ''BS.ByteString
    upal <- lift . lift . GHC.lookupId =<< thNameToGhcNameOrFail 'BSUnsafe.unsafePackAddressLen

    -- We construct the following expression:
    -- unsafePerformIO $ unsafePackAddressLen <length as int literal> <data as string literal address>
    -- This technique gratefully borrowed from the file-embed package

    -- The flags here are so GHC can check whether the int is in range for the current platform.
    let lenLit = GHC.mkIntExpr (GHC.targetPlatform flags) $ fromIntegral $ BS.length bs
    -- This will have type Addr#, which is right for unsafePackAddressLen
    let bsLit = GHC.Lit (GHC.LitString bs)
    let upaled = GHC.mkCoreApps (GHC.Var upal) [lenLit, bsLit]
    let upioed = GHC.mkCoreApps (GHC.Var upio) [GHC.Type (GHC.mkTyConTy bsTc), upaled]

    pure upioed

-- | Strips all enclosing 'GHC.Tick's off an expression.
stripTicks :: GHC.CoreExpr -> GHC.CoreExpr
stripTicks = \case
    GHC.Tick _ e -> stripTicks e
    e            -> e

-- | Helper to avoid doing too much construction of Core ourselves
mkCompiledCode :: forall a . BS.ByteString -> BS.ByteString -> BS.ByteString -> CompiledCode a
mkCompiledCode plcBS pirBS ci = SerializedCode plcBS (Just pirBS) (fold . unflat $ ci)

-- | Make a 'NameInfo' mapping the given set of TH names to their
-- 'GHC.TyThing's for later reference.
makePrimitiveNameInfo :: [TH.Name] -> PluginM uni fun NameInfo
makePrimitiveNameInfo names = do
    infos <- for names $ \name -> do
        ghcName <- thNameToGhcNameOrFail name
        thing <- lift . lift $ GHC.lookupThing ghcName
        pure (name, thing)
    pure $ Map.fromList infos
