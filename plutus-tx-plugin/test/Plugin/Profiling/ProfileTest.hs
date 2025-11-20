{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- | Standalone executable for profiling the plugin compilation functions.
--
-- This test uses the exposed 'runCompiler' from Plugin.hs to compile a simple
-- Core expression. This allows profiling the plugin code at runtime, including
-- the SCC annotations in Plugin.hs.
--
-- To run with profiling:
--   cabal build plutus-tx-plugin-profile-test --enable-profiling
--   cabal run plutus-tx-plugin-profile-test --enable-profiling -- +RTS -p -hc
module Main where

import Data.Default
import Data.Foldable (fold)
import PlutusCore qualified as PLC
import PlutusCore.Quote
import PlutusCore.Version qualified as PLC
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Compiler.Types qualified as PIR
import PlutusIR.Transform.RewriteRules
import PlutusIR.Transform.RewriteRules.RemoveTrace (rewriteRuleRemoveTrace)
import PlutusTx.Compiler.Types
import PlutusTx.Options (PluginOptions (..), defaultPluginOptions)
import PlutusTx.Plugin (runCompiler)

import GHC qualified as GHC
import GHC.Core.FamInstEnv qualified as GHC
import GHC.Core.Opt.OccurAnal qualified as GHC
import GHC.Driver.Session qualified as GHC
import GHC.Paths as GHC
import GHC.Plugins qualified as GHC

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Map qualified as Map

-- | Create a simple Core expression for testing (a literal integer)
createSimpleCoreExpr :: GHC.DynFlags -> GHC.CoreExpr
createSimpleCoreExpr _flags =
  let lit = GHC.Lit (GHC.LitNumber GHC.LitNumInt 42)
  in lit

-- | Set up a minimal CompileContext for testing
setupCompileContext
  :: GHC.DynFlags
  -> GHC.FamInstEnvs
  -> NameInfo
  -> CompileContext PLC.DefaultUni PLC.DefaultFun
setupCompileContext flags famEnvs nameInfo =
  let opts = defaultPluginOptions
      coverage = CoverageOpts mempty
   in CompileContext
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
        , ccModBreaks = Nothing
        , ccBuiltinsInfo = def
        , ccBuiltinCostModel = def
        , ccDebugTraceOn = _posDumpCompilationTrace opts
        , ccRewriteRules = makeRewriteRules opts
        , ccSafeToInline = False
        }
 where
  makeRewriteRules :: PluginOptions -> RewriteRules PLC.DefaultUni PLC.DefaultFun
  makeRewriteRules options =
    fold
      [ mwhen (_posRemoveTrace options) rewriteRuleRemoveTrace
      , defaultUniRewriteRules
      ]
  mwhen :: Monoid m => Bool -> m -> m
  mwhen b m = if b then m else mempty

-- | Create empty NameInfo (simplified - in real usage would need proper lookups)
createEmptyNameInfo :: NameInfo
createEmptyNameInfo = Map.empty

main :: IO ()
main = do
  putStrLn "Setting up for plugin profiling test..."

  -- Use GHC's API to get DynFlags
  GHC.defaultErrorHandler GHC.defaultFatalMessager GHC.defaultFlushOut $ do
    -- Initialize GHC session to get DynFlags
    GHC.runGhc (Just GHC.libdir) $ do
      -- Get DynFlags
      flags <- GHC.getSessionDynFlags

      -- Create a simple Core expression (literal integer)
      let expr = createSimpleCoreExpr flags

      -- Set up minimal context
      let famEnvs = (GHC.emptyFamInstEnv, GHC.emptyFamInstEnv)
          nameInfo = createEmptyNameInfo
          ctx = setupCompileContext flags famEnvs nameInfo
          opts = defaultPluginOptions
          st = CompileState 0 mempty
          moduleNameStr = "ProfileTest"
          -- Apply occurrence analysis like the plugin does
          expr' = GHC.occurAnalyseExpr expr

      -- Call runCompiler - this is where the SCC annotations are!
      _ <-
        runExceptT . runWriterT . runQuoteT . flip runReaderT ctx . flip evalStateT st $
          runCompiler moduleNameStr opts expr'

      pure ()
