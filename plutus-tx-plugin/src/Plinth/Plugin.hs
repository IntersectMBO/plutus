{-# LANGUAGE TemplateHaskellQuotes #-}

module Plinth.Plugin (plugin, plinthc) where

import PlutusTx.Options
import PlutusTx.Plugin.Boilerplate
import PlutusTx.Plugin.Common
import PlutusTx.Plugin.Timing
import PlutusTx.Plugin.Timing.Force
import PlutusTx.Plugin.Unsupported
import PlutusTx.Plugin.Utils

import Control.Exception (evaluate, throwIO)
import Control.Lens ((^.))
import Control.Monad.IO.Class (liftIO)
import Data.Either.Validation
import GHC.LanguageExtensions qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Tc.Types qualified as GHC

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.driverPlugin = \cliOpts environment -> do
        opts <- case parsePluginOptions (removeBoilerplateOpts cliOpts) of
          Success parsed -> pure parsed
          Failure errs -> throwIO errs
        timeStage
          (opts ^. posDumpTimings)
          "<driver>"
          "source.driver"
          ( \result ->
              GHC.xopt GHC.Strict (GHC.hsc_dflags result) `seq`
                GHC.gopt GHC.Opt_Strictness (GHC.hsc_dflags result) `seq`
                  ()
          )
          (addFlagsAndExts cliOpts environment)
    , GHC.typeCheckResultAction = \cliOpts _modSummary env -> do
        opts <- case parsePluginOptions (removeBoilerplateOpts cliOpts) of
          Success o -> pure o
          Failure errs -> liftIO $ throwIO errs
        let enabled = opts ^. posDumpTimings
            scope = GHC.moduleNameString (GHC.moduleName (GHC.tcg_mod env))
            measure stage = timeStage enabled scope stage forceSourceBinds
            maybeInjectAnchors =
              if opts ^. posPreserveSourceLocations then injectAnchors else pure
        if enabled then liftIO $ evaluate (forceSourceBinds env) else pure ()
        timeStage enabled scope "source.total" (const ()) $ do
          anchored <- measure "source.anchors" (maybeInjectAnchors env)
          supported <- measure "source.unsupported-markers" (injectUnsupportedMarkers anchored)
          measure "source.inlineable-pragmas" (addInlineables supported)
    , GHC.pluginRecompile = GHC.flagRecompile
    , GHC.installCoreToDos = installCorePlugin 'plinthc
    }
