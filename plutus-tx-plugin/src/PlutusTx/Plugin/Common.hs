{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
-- For some reason this module is very slow to compile otherwise
{-# OPTIONS_GHC -O0 #-}

module PlutusTx.Plugin.Common where

import Certifier (CertifierOutput (..), mkCertifier, prettyCertifierError, runCertifier)
import PlutusCore qualified as PLC
import PlutusCore.Compiler qualified as PLC
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Flat (Flat, flat, unflat)
import PlutusCore.Pretty as PLC
import PlutusCore.Quote
import PlutusCore.Version qualified as PLC
import PlutusIR qualified as PIR
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Compiler.Definitions qualified as PIR
import PlutusIR.Compiler.Provenance (noProvenance, original)
import PlutusIR.Compiler.Types qualified as PIR
import PlutusIR.Transform.RewriteRules
import PlutusIR.Transform.RewriteRules.RemoveTrace (rewriteRuleRemoveTrace)
import PlutusPrelude
import PlutusTx.AsData.Internal qualified
import PlutusTx.Bool ((&&), (||))
import PlutusTx.Builtins (equalsInteger, mkNil, mkNilOpaque, useFromOpaque, useToOpaque)
import PlutusTx.Code
import PlutusTx.Compiler.Builtins
import PlutusTx.Compiler.Compat qualified as Compat
import PlutusTx.Compiler.Error
import PlutusTx.Compiler.Expr
import PlutusTx.Compiler.Types
import PlutusTx.Coverage
import PlutusTx.Function qualified
import PlutusTx.List qualified
import PlutusTx.Optimize.Inline qualified
import PlutusTx.Options
import PlutusTx.PIRTypes
import PlutusTx.PLCTypes
import PlutusTx.Plugin.Boilerplate (removeBoilerplateOpts)
import PlutusTx.Plugin.Utils qualified
import PlutusTx.Trace
import UntypedPlutusCore qualified as UPLC

import GHC.ByteCode.Types qualified as GHC
import GHC.Core.Coercion.Opt qualified as GHC
import GHC.Core.FamInstEnv qualified as GHC
import GHC.Core.Opt.Arity qualified as GHC
import GHC.Core.Opt.OccurAnal qualified as GHC
import GHC.Core.Opt.Simplify qualified as GHC
import GHC.Core.Opt.Simplify.Env qualified as GHC
import GHC.Core.Opt.Simplify.Monad qualified as GHC
import GHC.Core.Rules.Config qualified as GHC
import GHC.Core.TyCo.Rep qualified as GHC
import GHC.Core.Unfold qualified as GHC
import GHC.Hs qualified as GHC
import GHC.Hs.Syn.Type qualified as GHC
import GHC.Iface.Env qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Tc.Types qualified as GHC
import GHC.Tc.Types.Evidence qualified as GHC
import GHC.Tc.Utils.Env qualified as GHC
import GHC.Tc.Utils.Monad qualified as GHC
import GHC.Types.TyThing qualified as GHC
import GHC.Unit.Finder qualified as GHC

import Control.Exception (SomeException, throwIO, try)
import Control.Lens
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe qualified as BSUnsafe
import Data.Either.Validation
import Data.Generics.Uniplate.Data
import Data.Map qualified as Map
import Data.Maybe (fromJust, mapMaybe, maybeToList)
import Data.Monoid.Extra (mwhen)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Num.Integer qualified
import Language.Haskell.TH.Syntax as TH hiding (lift)
import Prettyprinter qualified as PP
import System.IO (hPutStrLn, openBinaryTempFile, stderr)
import System.IO.Unsafe (unsafePerformIO)

data PluginCtx = PluginCtx
  { pcOpts :: PluginOptions
  , pcFamEnvs :: GHC.FamInstEnvs
  , pcMarkerName :: GHC.Name
  , pcAnchorName :: GHC.Name
  , pcModuleName :: GHC.ModuleName
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

installCorePlugin
  :: TH.Name
  -> [GHC.CommandLineOption]
  -> [GHC.CoreToDo]
  -> GHC.CoreM [GHC.CoreToDo]
installCorePlugin markerTHName args rest = do
  -- create simplifier pass to be placed at the front
  simplPass <- mkSimplPass <$> GHC.getDynFlags
  -- instantiate our plugin pass
  pluginPass <-
    mkPluginPass markerTHName <$> case parsePluginOptions (removeBoilerplateOpts args) of
      Success opts -> pure opts
      Failure errs -> liftIO $ throwIO errs
  -- return the pipeline
  pure $
    simplPass
      : pluginPass
      : rest

plinthcModName, anchorName :: String
plinthcModName = fromJust $ TH.nameModule 'PlutusTx.Plugin.Utils.anchor
anchorName = TH.nameBase 'PlutusTx.Plugin.Utils.anchor

-- | Wrap certain @HsExpr@s in the typed checked module with @anchor@.
injectAnchors
  :: GHC.TcGblEnv
  -> GHC.TcM GHC.TcGblEnv
injectAnchors env = do
  hscEnv <- GHC.getTopEnv
  findResult <-
    liftIO $
      GHC.findImportedModule
        hscEnv
        (GHC.mkModuleName plinthcModName)
        GHC.NoPkgQual
  anchorId <- case findResult of
    GHC.Found _ m -> do
      GHC.tcLookupId =<< GHC.lookupOrig m (GHC.mkVarOcc anchorName)
    _ ->
      GHC.pprPanic
        "Plinth.Plugin"
        (GHC.text $ "Could not find module " <> plinthcModName)
  let binds = GHC.tcg_binds env
      bindsAnchored =
        Compat.modifyBinds
          (transformBi (stripGuardAnchors anchorId) . transformBi (anchorExpr anchorId))
          binds
  pure env {GHC.tcg_binds = bindsAnchored}

-- | Wrap an @HsExpr@ with @anchor@.
anchorExpr :: GHC.Id -> GHC.LHsExpr GHC.GhcTc -> GHC.LHsExpr GHC.GhcTc
anchorExpr anchorId le@(GHC.L ann e)
  | isAnchorWorthy anchorId e
  , Just !sp <- GHC.srcSpanToRealSrcSpan (GHC.locA ann) =
      let locStr = encodeSrcSpan sp
          locTy = GHC.LitTy (GHC.StrTyLit (GHC.mkFastString locStr))
          exprTy = GHC.hsExprType e
          wrapper = GHC.WpTyApp exprTy `GHC.WpCompose` GHC.WpTyApp locTy
          anchor = GHC.mkHsWrap wrapper (GHC.HsVar GHC.noExtField $ GHC.noLocA anchorId)
       in GHC.noLocA (Compat.hsAppTc (GHC.noLocA anchor) le)
  | otherwise = le

isAnchorWorthy :: GHC.Id -> GHC.HsExpr GHC.GhcTc -> Bool
isAnchorWorthy marker expr
  -- This should never happen since we add anchors bottom-up, but just in case.
  | isAnchorApp marker expr = False
  -- @anchor@ only works on lifted types
  | GHC.mightBeUnliftedType (GHC.hsExprType expr) = False
  | otherwise = case expr of
      -- We currently only wrap variables with @anchor@. Wrapping more
      -- expressions leads to significantly less optimized GHC Core, because
      -- GHC is unable to optimize it effectively.
      --
      -- However, this should be exactly what we want! Ideally we'd avoid any GHC
      -- optimizations since they don't necessarily preserve Plinth semantics. All
      -- optimization should instead be performed by the PIR/UPLC optimizers. This
      -- suggests there's still significant room for improvement in the PIR/UPLC optimizers.
      GHC.HsVar {} -> True
      _ -> False

isTick :: GHC.HsExpr GHC.GhcTc -> Bool
isTick = \case
  GHC.XExpr (GHC.HsTick _ _) -> True
  _ -> False

isAnchorApp :: GHC.Id -> GHC.HsExpr GHC.GhcTc -> Bool
isAnchorApp marker = (Just marker ==) . appHead
  where
    appHead = \case
      GHC.HsVar _ (GHC.L _ v) -> Just v
      GHC.HsApp _ (GHC.L _ f) _ -> appHead f
      Compat.HsAppType _ (GHC.L _ f) _ -> appHead f
      GHC.XExpr (Compat.WrapExpr e) -> appHead e
      Compat.HsPar (GHC.L _ e) -> appHead e
      _ -> Nothing

{-| Remove anchors in guards. We can't wrap `otherwise` with an anchor, since it would
cause GHC to emit a "non-exhuastive" warning. In general, anchors in guards are
probably not very useful, so we remove all anchors within guards. -}
stripGuardAnchors
  :: GHC.Id
  -> GHC.GRHS GHC.GhcTc (GHC.LHsExpr GHC.GhcTc)
  -> GHC.GRHS GHC.GhcTc (GHC.LHsExpr GHC.GhcTc)
stripGuardAnchors anchorId (GHC.GRHS x guards body) =
  GHC.GRHS x (transformBi (stripHsAnchor anchorId) guards) body

stripHsAnchor :: GHC.Id -> GHC.LHsExpr GHC.GhcTc -> GHC.LHsExpr GHC.GhcTc
stripHsAnchor anchorId le@(GHC.L _ e)
  | GHC.HsApp _ (GHC.L _ f) arg <- e
  , isAnchor f =
      arg
  | otherwise = le
  where
    isAnchor = \case
      GHC.HsVar _ (GHC.L _ v) -> v == anchorId
      GHC.XExpr (Compat.WrapExpr inner) -> isAnchor inner
      _ -> False

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

Note also, this `sm_pre_inline` pass doesn't include some of the inlining GHC does before the
plugin.
The GHC desugarer generates a large number of intermediate definitions and general clutter that
should be removed quickly. So GHC's "simple optimiser" (GHC.Core.SimpleOpt) also inlines things with
single occurrences. This is why the OPAQUE pragma is needed to avoid inlining of bindings that
have single occurrence.
None of -fmax-simplifier-iterations=0  -fforce-recomp -O0 would prevent it,
nor will turning off `sm_pre_inline`.
See https://gitlab.haskell.org/ghc/ghc/-/issues/23337.
-}

-- | A simplifier pass, implemented by GHC
mkSimplPass :: GHC.DynFlags -> GHC.CoreToDo
mkSimplPass dflags =
  -- See Note [Making sure unfoldings are present]
  GHC.CoreDoSimplify $
    GHC.SimplifyOpts
      { GHC.so_dump_core_sizes = False
      , GHC.so_iterations = 1
      , GHC.so_mode = simplMode
      , GHC.so_pass_result_cfg = Nothing
      , GHC.so_hpt_rules = GHC.emptyRuleBase
      , GHC.so_top_env_cfg = GHC.TopEnvConfig 0 0
      }
  where
    simplMode =
      GHC.SimplMode
        { GHC.sm_names = ["Ensure unfoldings are present"]
        , GHC.sm_phase = GHC.InitialPhase
        , GHC.sm_uf_opts = GHC.defaultUnfoldingOpts
        , GHC.sm_rules = False
        , GHC.sm_cast_swizzle = True
        , -- See Note [GHC.sm_pre_inline]
          GHC.sm_pre_inline = True
        , -- You might think you would need this, but apparently not
          GHC.sm_inline = False
        , GHC.sm_case_case = False
        , GHC.sm_eta_expand = False
        , GHC.sm_float_enable = GHC.FloatDisabled
        , GHC.sm_do_eta_reduction = False
        , GHC.sm_arity_opts = GHC.ArityOpts False False
        , GHC.sm_rule_opts = GHC.RuleOpts (GHC.targetPlatform dflags) False True False
        , GHC.sm_case_folding = False
        , GHC.sm_case_merge = False
        , GHC.sm_co_opt_opts = GHC.OptCoercionOpts False
        }

{- Note [Marker resolution]
We use TH's 'foo exact syntax for resolving the marker's ghc name, as explained in:
<https://hackage.haskell.org/package/ghc-9.6.6/docs/GHC-Plugins.html#v:thNameToGhcName>

The GHC haddock suggests that the "exact syntax" will always succeed because it is statically
resolved here (inside this Plugin module);

If this is the case, then it means that our plugin will always traverse each module's binds
searching for the marker even in the case that the marker name is not in scope locally in the module
 under compilation.

The alternative is to use the "dynamic syntax" (`TH.mkName "plc"`), which implies that
the "plc" name will be resolved dynamically during module's compilation. In case "plc" is not
locally in scope,
the plugin would finish faster by completely skipping the module under compilation.
This dynamic approach comes with its own downsides however,
because the user may have imported "plc" qualified or aliased it, which will fail to resolve.
-}

{-| Our plugin works at haskell-module level granularity; the plugin
looks at the module's top-level bindings for markers and compiles their right-hand-side core
expressions. -}
mkPluginPass :: TH.Name -> PluginOptions -> GHC.CoreToDo
mkPluginPass markerTHName opts = GHC.CoreDoPluginPass "Core to PLC" $ \guts -> do
  -- Family env code borrowed from SimplCore
  p_fam_env <- GHC.getPackageFamInstEnv
  -- See Note [Marker resolution]
  maybeMarkerName <- GHC.thNameToGhcName markerTHName
  maybeanchorGhcName <- GHC.thNameToGhcName 'PlutusTx.Plugin.Utils.anchor
  case (maybeMarkerName, maybeanchorGhcName) of
    -- See Note [Marker resolution]
    (Just markerName, Just anchorGhcName) ->
      let pctx =
            PluginCtx
              { pcOpts = opts
              , pcFamEnvs = (p_fam_env, GHC.mg_fam_inst_env guts)
              , pcMarkerName = markerName
              , pcAnchorName = anchorGhcName
              , pcModuleName = GHC.moduleName $ GHC.mg_module guts
              , pcModuleModBreaks = GHC.mg_modBreaks guts
              }
       in -- start looking for marker calls from the top-level binds
          GHC.bindsOnlyPass (runPluginM pctx . traverse compileBind) guts
    _ -> pure guts

{-| The monad where the plugin runs in for each module.
It is a core->core compiler monad, called PluginM, augmented with pure errors. -}
type PluginM uni fun = ReaderT PluginCtx (ExceptT (CompileError uni fun Ann) GHC.CoreM)

-- | Runs the plugin monad in a given context; throws a Ghc.Exception when compilation fails.
runPluginM
  :: forall uni fun a
   . (PLC.PrettyUni uni, PP.Pretty fun)
  => PluginCtx -> PluginM uni fun a -> GHC.CoreM a
runPluginM pctx act = do
  res <- runExceptT $ runReaderT act pctx
  case res of
    Right x -> pure x
    Left err -> liftIO $ do
      let errStack :: (Error uni fun Ann, [(Int, (Text, Maybe GHC.RealSrcSpan))])
          errStack = second reverse $ go err
            where
              go = \case
                NoContext e -> (e, [])
                WithContextC p c rest ->
                  let (e, cs) = go rest
                   in (e, (p, c) : cs)

          truncated :: ([(Int, (Text, Maybe GHC.RealSrcSpan))], Maybe GHC.RealSrcSpan)
          truncated = go (snd errStack) Nothing
            where
              go [] loc = ([], loc)
              go (x : xs) loc = case x of
                (_, (_, Just ss)) -> ([x], Just ss)
                (_, (_, Nothing)) ->
                  let (ys, ss) = go xs loc
                   in (x : ys, ss)

          err' :: CompileError uni fun Ann
          err' = foldl' (\e (p, c) -> WithContextC p c e) (NoContext (fst errStack)) (fst truncated)

      snippet <- case snd truncated of
        Nothing -> pure Nothing
        Just ss -> getSourceSnippet ss

      let msg =
            PP.vsep $
              [ "Plinth Compilation Error:"
              , PP.pretty (mapContext fst err')
              ]
                ++ maybeToList snippet
          errInGhc = GHC.ProgramError . show $ msg
      GHC.throwGhcExceptionIO errInGhc

getSourceSnippet :: GHC.RealSrcSpan -> IO (Maybe (PP.Doc ann))
getSourceSnippet ss = do
  let file = GHC.unpackFS (GHC.srcSpanFile ss)
      sLine = GHC.srcSpanStartLine ss
      sCol = GHC.srcSpanStartCol ss
      eLine = GHC.srcSpanEndLine ss
      eCol = GHC.srcSpanEndCol ss
  result <- try @SomeException (readFile file)
  pure $ case result of
    Left _ -> Nothing
    Right (lines -> ls)
      | sLine >= 1 Prelude.&& sLine <= length ls ->
          let l = ls !! (sLine - 1)
              endCol = if eLine == sLine then eCol else length l + 1
           in Just (formatSourceSnippet sLine sCol endCol l)
      | otherwise -> Nothing

formatSourceSnippet :: Int -> Int -> Int -> String -> PP.Doc ann
formatSourceSnippet lineNum startCol0 endCol0 l0 = PP.vsep [preCode, numberedLine, postCode]
  where
    (l, reduced) = reduceIndent l0
    startCol = startCol0 - reduced
    endCol = endCol0 - reduced
    k = length (show lineNum)
    preCode = PP.pretty (replicate k ' ') <> PP.pretty @String " |ᴾᴸᴵᴺᵀᴴ"
    numberedLine = PP.pretty lineNum <> PP.pretty @String " | " <> PP.pretty l
    carets = replicate (max 1 (endCol - startCol)) '^'
    postCode =
      PP.pretty (replicate k ' ')
        <> PP.pretty @String " | "
        <> PP.pretty (replicate (startCol - 1) ' ')
        <> red (PP.pretty carets)
    reduceIndent :: String -> (String, Int)
    reduceIndent s
      | ind >= 5 = (replicate 5 ' ' ++ rest, ind - 5)
      | otherwise = (s, 0)
      where
        (spaces, rest) = span (== ' ') s
        ind = length spaces
    red :: PP.Doc ann -> PP.Doc ann
    red doc = PP.pretty ("\ESC[32m" :: String) <> doc <> PP.pretty ("\ESC[0m" :: String)

-- | Compiles all the marked expressions in the given binder into PLC literals.
compileBind :: GHC.CoreBind -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreBind
compileBind = \case
  GHC.NonRec b rhs -> GHC.NonRec b <$> compileMarkedExprs rhs
  GHC.Rec bindsRhses ->
    GHC.Rec
      <$> ( for bindsRhses $ \(b, rhs) -> do
              rhs' <- compileMarkedExprs rhs
              pure (b, rhs')
          )

{- Note [Hooking in the plugin]
Working out what to process and where to put it is tricky. We are going to turn the result in
to a 'CompiledCode', not the Haskell expression we started with!

Currently we look for calls to the @marker :: a -> CompiledCode a@ function,
where @marker@ can be @plc@ or @plinthc@,
and we replace the whole application with the generated code object, which will still be well-typed.
-}

{- Note [Polymorphic values and Any]
If you try and use the plugin on a polymorphic expression, then GHC will replace the quantified
types with 'Any' and remove the type lambdas. This is pretty annoying, and I don't entirely
understand why it happens, despite poking around in GHC a fair bit.

Possibly it has to do with the type that is given to the marker being unconstrained, resulting in GHC
putting 'Any' there, and that then propagating into the type of the quote. It's tricky to experiment
with this, since you can't really specify a polymorphic type in a type application or in the
resulting 'CompiledCode' because that's impredicative polymorphism.
-}

{-| Compiles all the core-expressions surrounded by the marker in the given expression
into PLC literals. -}
compileMarkedExprs :: GHC.CoreExpr -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreExpr
compileMarkedExprs expr = do
  markerName <- asks pcMarkerName
  anchorGhcName <- asks pcAnchorName
  case expr of
    -- This clause is for the `plc` marker. It can be removed when we remove `plc`.
    GHC.App
      ( GHC.App
          ( GHC.App
              ( GHC.App
                  -- function id
                  -- sometimes GHCi sticks ticks around this for some reason
                  (stripTicks -> (GHC.Var fid))
                  -- first type argument, must be a string literal type
                  (GHC.Type (GHC.isStrLitTy -> Just fs_locStr))
                )
              -- second type argument
              (GHC.Type codeTy)
            )
          _
        )
      -- value argument
      inner
        | markerName == GHC.idName fid -> compileMarkedExprOrDefer (show fs_locStr) codeTy inner
    GHC.App
      ( GHC.App
          (stripCoreAnchors anchorGhcName -> (GHC.Var fid))
          (stripCoreAnchors anchorGhcName -> GHC.Type codeTy)
        )
      -- code to be compiled
      inner
        | markerName == GHC.idName fid -> compileMarkedExprOrDefer "" codeTy inner
    e@(GHC.Var fid)
      | markerName == GHC.idName fid ->
          throwError . NoContext . InvalidMarkerError . GHC.showSDocUnsafe $ GHC.ppr e
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

{-| Behaves the same as 'compileMarkedExpr', unless a compilation error occurs ;
if a compilation error happens and the 'defer-errors' option is turned on,
the compilation error is suppressed and the original hs expression is replaced with a
haskell runtime-error expression. -}
compileMarkedExprOrDefer
  :: String -> GHC.Type -> GHC.CoreExpr -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreExpr
compileMarkedExprOrDefer locStr codeTy origE = do
  opts <- asks pcOpts
  let compileAct = compileMarkedExpr locStr codeTy origE
  if _posDeferErrors opts
    -- TODO: we could perhaps move this catchError to the "runExceptT" module-level, but
    -- it leads to uglier code and difficulty of handling other pure errors
    then compileAct `catchError` emitRuntimeError codeTy
    else compileAct

{-| Given an expected Haskell type 'a', it generates Haskell code which throws a GHC runtime error
\"as\" 'CompiledCode a'. -}
emitRuntimeError
  :: (PLC.PrettyUni uni, PP.Pretty fun)
  => GHC.Type -> CompileError uni fun Ann -> PluginM uni fun GHC.CoreExpr
emitRuntimeError codeTy e = do
  opts <- asks pcOpts
  let shown = show $ PP.pretty (pruneContext (_posContextLevel opts) $ mapContext fst e)
  tcName <- thNameToGhcNameOrFail ''CompiledCode
  tc <- lift . lift $ GHC.lookupTyCon tcName
  pure $ GHC.mkImpossibleExpr (GHC.mkTyConApp tc [codeTy]) shown

{-| Compile the core expression that is surrounded by a 'plc' marker,
and return a core expression which evaluates to the compiled plc AST as a serialized bytestring,
to be injected back to the Haskell program. -}
compileMarkedExpr
  :: String -> GHC.Type -> GHC.CoreExpr -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreExpr
compileMarkedExpr _locStr codeTy origE = do
  flags <- GHC.getDynFlags
  famEnvs <- asks pcFamEnvs
  opts <- asks pcOpts
  moduleName <- asks pcModuleName
  let moduleNameStr =
        GHC.showSDocForUser flags GHC.emptyUnitState GHC.alwaysQualify (GHC.ppr moduleName)
  -- We need to do this out here, since it has to run in CoreM
  nameInfo <-
    makePrimitiveNameInfo $
      builtinNames
        ++ [ ''Bool
           , 'False
           , 'True
           , 'traceBool
           , 'GHC.Num.Integer.integerNegate
           , '(PlutusTx.Bool.&&)
           , '(PlutusTx.Bool.||)
           , '(PlutusTx.List.!!)
           , 'PlutusTx.AsData.Internal.wrapTail
           , 'PlutusTx.AsData.Internal.wrapUnsafeDataAsConstr
           , 'PlutusTx.AsData.Internal.droppableUnsafeCaseList
           , 'PlutusTx.Function.fix
           , 'PlutusTx.Optimize.Inline.inline
           , 'useToOpaque
           , 'useFromOpaque
           , 'mkNilOpaque
           , 'mkNil
           , 'PlutusTx.Builtins.equalsInteger
           , 'PlutusTx.Plugin.Utils.anchor
           , 'PlutusTx.Plugin.Utils.unsupported
           ]
  modBreaks <- asks pcModuleModBreaks
  let coverage =
        CoverageOpts . Set.fromList $
          [l | _posCoverageAll opts, l <- [minBound .. maxBound]]
            ++ [LocationCoverage | _posCoverageLocation opts]
            ++ [BooleanCoverage | _posCoverageBoolean opts]
  let ctx =
        CompileContext
          { ccOpts =
              CompileOptions
                { coProfile = _posProfile opts
                , coCoverage = coverage
                , coDatatypeStyle =
                    if _posPlcTargetVersion opts < PLC.plcVersion110
                      then PIR.ScottEncoding
                      else PIR._dcoStyle $ _posDatatypes opts
                , coRemoveTrace = _posRemoveTrace opts
                , coInlineFix = _posInlineFix opts
                }
          , ccFlags = flags
          , ccFamInstEnvs = famEnvs
          , ccNameInfo = nameInfo
          , ccScope = initialScope
          , ccBlackholed = mempty
          , ccCurDef = Nothing
          , ccModBreaks = modBreaks
          , ccBuiltinsInfo = def
          , ccBuiltinCostModel = def
          , ccDebugTraceOn = _posDumpCompilationTrace opts
          , ccRewriteRules = makeRewriteRules opts
          , ccSafeToInline = False
          }
      st = CompileState 0 mempty
  -- See Note [Occurrence analysis]
  let origE' = GHC.occurAnalyseExpr origE

  ((pirP, uplcP), covIdx) <-
    runWriterT . runQuoteT . flip runReaderT ctx . flip evalStateT st $
      runCompiler moduleNameStr opts origE'

  -- serialize the PIR, PLC, and coverageindex outputs into a bytestring.
  bsPir <- makeByteStringLiteral $ flat pirP
  bsPlc <- makeByteStringLiteral $ flat (UPLC.UnrestrictedProgram uplcP)
  covIdxFlat <- makeByteStringLiteral $ flat covIdx

  builder <- lift . lift . GHC.lookupId =<< thNameToGhcNameOrFail 'mkCompiledCode

  -- inject the three bytestrings back as Haskell code.
  pure $
    GHC.Var builder
      `GHC.App` GHC.Type codeTy
      `GHC.App` bsPlc
      `GHC.App` bsPir
      `GHC.App` covIdxFlat

{-| The GHC.Core to PIR to PLC compiler pipeline. Returns both the PIR and PLC output.
It invokes the whole compiler chain:  Core expr -> PIR expr -> PLC expr -> UPLC expr. -}
runCompiler
  :: forall uni fun m
   . ( uni ~ PLC.DefaultUni
     , fun ~ PLC.DefaultFun
     , MonadReader (CompileContext uni fun) m
     , MonadState CompileState m
     , MonadWriter CoverageIndex m
     , MonadQuote m
     , MonadError (CompileError uni fun Ann) m
     , MonadIO m
     )
  => String
  -> PluginOptions
  -> GHC.CoreExpr
  -> m (PIRProgram uni fun, UPLCProgram uni fun)
runCompiler moduleName opts expr = do
  GHC.DynFlags {GHC.extensions = extensions} <- asks ccFlags
  let
    enabledExtensions =
      mapMaybe
        ( \case
            GHC.On a -> Just a
            GHC.Off _ -> Nothing
        )
        extensions
    extensionBlacklist =
      [ GADTs
      , PolyKinds
      ]
    unsupportedExtensions =
      filter (`elem` extensionBlacklist) enabledExtensions

  unless (null unsupportedExtensions) $
    throwPlain $
      UnsupportedError $
        "Following extensions are not supported: "
          <> Text.intercalate ", " (Text.pack . show <$> unsupportedExtensions)

  -- Plc configuration
  plcTcConfig <-
    modifyError (NoContext . PIRError . PIR.PLCTypeError) $
      PLC.getDefTypeCheckConfig PIR.noProvenance
  datatypeStyle <- asks $ coDatatypeStyle . ccOpts
  let plcVersion = opts ^. posPlcTargetVersion
      hints = UPLC.InlineHints $ \ann _ -> case ann of
        -- See Note [The problem of inlining destructors]
        -- We want to inline destructors, but even in UPLC our inlining heuristics
        -- aren't quite smart enough to tell that they're good inlining candidates,
        -- so we just explicitly tell the inliner to inline them all.
        --
        -- In fact, this instructs the inliner to inline *any* binding inside a destructor,
        -- which is a slightly large hammer but is actually what we want since it will mean
        -- that we also aggressively reduce the bindings inside the destructor.
        PIR.DatatypeComponent PIR.Destructor _ -> AlwaysInline
        _
          | AlwaysInline `elem` fmap annInline (toList ann) -> AlwaysInline
          | SafeToInline `elem` fmap annInline (toList ann) -> SafeToInline
          | otherwise -> MayInline

  rewriteRules <- asks ccRewriteRules

  -- Compilation configuration
  -- pir's tc-config is based on plc tcconfig
  let pirTcConfig = PIR.PirTCConfig plcTcConfig PIR.YesEscape
      pirCtx =
        PIR.toDefaultCompilationCtx plcTcConfig
          & set (PIR.ccOpts . PIR.coOptimize) (opts ^. posOptimize)
          & set (PIR.ccOpts . PIR.coTypecheck) (opts ^. posDoTypecheck)
          & set (PIR.ccOpts . PIR.coPedantic) (opts ^. posPedantic)
          & set (PIR.ccOpts . PIR.coVerbose) (opts ^. posVerbosity == Verbose)
          & set (PIR.ccOpts . PIR.coDebug) (opts ^. posVerbosity == Debug)
          & set
            (PIR.ccOpts . PIR.coMaxSimplifierIterations)
            (opts ^. posMaxSimplifierIterationsPir)
          & set PIR.ccTypeCheckConfig pirTcConfig
          -- Simplifier options
          & set
            (PIR.ccOpts . PIR.coDoSimplifierUnwrapCancel)
            (opts ^. posDoSimplifierUnwrapCancel)
          & set
            (PIR.ccOpts . PIR.coDoSimplifierBeta)
            (opts ^. posDoSimplifierBeta)
          & set
            (PIR.ccOpts . PIR.coDoSimplifierInline)
            (opts ^. posDoSimplifierInline)
          & set
            (PIR.ccOpts . PIR.coDoSimplifierEvaluateBuiltins)
            (opts ^. posDoSimplifierEvaluateBuiltins)
          & set
            (PIR.ccOpts . PIR.coDoSimplifierStrictifyBindings)
            (opts ^. posDoSimplifierStrictifyBindings)
          & set
            (PIR.ccOpts . PIR.coDoSimplifierRemoveDeadBindings)
            (opts ^. posDoSimplifierRemoveDeadBindings)
          & set
            (PIR.ccOpts . PIR.coInlineConstants)
            (opts ^. posInlineConstants)
          & set
            (PIR.ccOpts . PIR.coInlineFix)
            (opts ^. posInlineFix)
          & set (PIR.ccOpts . PIR.coInlineHints) hints
          & set
            (PIR.ccOpts . PIR.coInlineCallsiteGrowth)
            (opts ^. posInlineCallsiteGrowth . to fromIntegral)
          & set (PIR.ccOpts . PIR.coRelaxedFloatin) (opts ^. posRelaxedFloatin)
          & set
            (PIR.ccOpts . PIR.coCaseOfCaseConservative)
            (opts ^. posCaseOfCaseConservative)
          & set (PIR.ccOpts . PIR.coPreserveLogging) (opts ^. posPreserveLogging)
          & set (PIR.ccOpts . PIR.coDatatypes . PIR.dcoStyle) datatypeStyle
          -- TODO: ensure the same as the one used in the plugin
          & set PIR.ccBuiltinsInfo def
          & set PIR.ccBuiltinCostModel def
          & set PIR.ccRewriteRules rewriteRules
      plcOpts =
        PLC.defaultCompilationOpts
          & set
            (PLC.coOptimizeOpts . UPLC.ooMaxSimplifierIterations)
            (opts ^. posMaxSimplifierIterationsUPlc)
          & set
            (PLC.coOptimizeOpts . UPLC.ooCseWhichSubterms)
            (opts ^. posCseWhichSubterms)
          & set
            (PLC.coOptimizeOpts . UPLC.ooMaxCseIterations)
            (opts ^. posMaxCseIterations)
          & set
            (PLC.coOptimizeOpts . UPLC.ooConservativeOpts)
            (opts ^. posConservativeOpts)
          & set (PLC.coOptimizeOpts . UPLC.ooInlineHints) hints
          & set
            (PLC.coOptimizeOpts . UPLC.ooInlineConstants)
            (opts ^. posInlineConstants)
          & set
            (PLC.coOptimizeOpts . UPLC.ooInlineCallsiteGrowth)
            (opts ^. posInlineCallsiteGrowth . to fromIntegral)
          & set
            (PLC.coOptimizeOpts . UPLC.ooPreserveLogging)
            (opts ^. posPreserveLogging)
          & set
            (PLC.coOptimizeOpts . UPLC.ooApplyToCase)
            (opts ^. posApplyToCase)
          & set
            (PLC.coOptimizeOpts . UPLC.ooCertifiedOptsOnly)
            (opts ^. posCertifiedOptsOnly)

  -- GHC.Core -> Pir translation.
  pirT <- original <$> (PIR.runDefT annMayInline $ compileExprWithDefs expr)
  let pirP = PIR.Program noProvenance plcVersion pirT
  when (opts ^. posDumpPir) . liftIO $
    dumpFlat (void pirP) "initial PIR program" (moduleName ++ "_initial.pir-flat")

  -- Pir -> (Simplified) Pir pass. We can then dump/store a more legible PIR program.
  spirP <-
    flip runReaderT pirCtx $
      modifyError (NoContext . PIRError) $
        PIR.compileToReadable pirP
  when (opts ^. posDumpPir) . liftIO $
    dumpFlat (void spirP) "simplified PIR program" (moduleName ++ "_simplified.pir-flat")

  -- (Simplified) Pir -> Plc translation.
  plcP <-
    flip runReaderT pirCtx $
      modifyError (NoContext . PIRError) $
        PIR.compileReadableToPlc spirP
  when (opts ^. posDumpPlc) . liftIO $
    dumpFlat (void plcP) "typed PLC program" (moduleName ++ ".tplc-flat")

  -- We do this after dumping the programs so that if we fail typechecking we still get the dump.
  when (opts ^. posDoTypecheck) . void $
    liftExcept $
      modifyError PLC.TypeErrorE $
        PLC.inferTypeOfProgram plcTcConfig (plcP $> annMayInline)

  let optCertify = opts ^. posCertify
  (uplcP, simplTrace) <- flip runReaderT plcOpts $ PLC.compileProgramWithTrace plcP
  liftIO $ case optCertify of
    Just certName -> do
      -- FIXME: add a plugin option to choose from BasicOutput vs. other options
      result <- runCertifier $ mkCertifier simplTrace certName BasicOutput []
      case result of
        Right _ -> pure ()
        Left err ->
          hPutStrLn stderr $ prettyCertifierError err
    Nothing -> pure ()

  dbP <-
    liftExcept $ modifyError PLC.FreeVariableErrorE $ traverseOf UPLC.progTerm UPLC.deBruijnTerm uplcP
  when (opts ^. posDumpUPlc) . liftIO $
    dumpFlat
      (UPLC.UnrestrictedProgram $ void dbP)
      "untyped PLC program"
      (moduleName ++ ".uplc-flat")
  -- Discard the Provenance information at this point, just keep the SrcSpans
  -- TODO: keep it and do something useful with it
  pure (fmap getSrcSpans spirP, fmap getSrcSpans dbP)
  where
    -- ugly trick to take out the concrete plc.error and in case of error, map it / rethrow it
    --  using our 'CompileError'
    liftExcept :: ExceptT (PLC.Error PLC.DefaultUni PLC.DefaultFun Ann) m b -> m b
    liftExcept = modifyError (NoContext . PLCError)

    dumpFlat :: Flat t => t -> String -> String -> IO ()
    dumpFlat t desc fileName = do
      (tPath, tHandle) <- openBinaryTempFile "." fileName
      putStrLn $ "!!! dumping " ++ desc ++ " to " ++ show tPath
      BS.hPut tHandle $ flat t

    getSrcSpans :: PIR.Provenance Ann -> SrcSpans
    getSrcSpans = SrcSpans . Set.unions . fmap (unSrcSpans . annSrcSpans) . toList

-- | Get the 'GHC.Name' corresponding to the given 'TH.Name', or throw an error if we can't get it.
thNameToGhcNameOrFail :: TH.Name -> PluginM uni fun GHC.Name
thNameToGhcNameOrFail name = do
  maybeName <- lift . lift $ GHC.thNameToGhcName name
  case maybeName of
    Just n -> pure n
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
  -- unsafePerformIO $
  --     unsafePackAddressLen <length as int literal> <data as string literal address>
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
  e -> e

stripCoreAnchors :: GHC.Name -> GHC.CoreExpr -> GHC.CoreExpr
stripCoreAnchors marker = \case
  GHC.Tick _ e -> stripCoreAnchors marker e
  GHC.App (GHC.App (GHC.App (GHC.Var f) _locTy) _codeTy) code
    | GHC.getName f == marker -> stripCoreAnchors marker code
  other -> other

-- | Helper to avoid doing too much construction of Core ourselves
mkCompiledCode :: forall a. BS.ByteString -> BS.ByteString -> BS.ByteString -> CompiledCode a
mkCompiledCode plcBS pirBS ci = SerializedCode plcBS (Just pirBS) (fold . unflat $ ci)

{-| Make a 'NameInfo' mapping the given set of TH names to their
'GHC.TyThing's for later reference. -}
makePrimitiveNameInfo :: [TH.Name] -> PluginM uni fun NameInfo
makePrimitiveNameInfo names = do
  infos <- for names $ \name -> do
    ghcName <- thNameToGhcNameOrFail name
    thing <- lift . lift $ GHC.lookupThing ghcName
    pure (name, thing)
  pure $ Map.fromList infos

makeRewriteRules :: PluginOptions -> RewriteRules DefaultUni DefaultFun
makeRewriteRules options =
  fold
    [ mwhen (options ^. posRemoveTrace) rewriteRuleRemoveTrace
    , defaultUniRewriteRules
    ]
