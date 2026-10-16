{-# LANGUAGE TemplateHaskellQuotes #-}

module Plinth.Plugin (plugin, plinthc) where

import PlutusTx.Options
import PlutusTx.Plugin.Boilerplate
import PlutusTx.Plugin.Common
import PlutusTx.Plugin.Timing
import PlutusTx.Plugin.Unsupported
import PlutusTx.Plugin.Utils

import Control.Exception (throwIO)
import Control.Lens ((^.))
import Control.Monad.IO.Class (liftIO)
import Data.Either.Validation
import GHC.LanguageExtensions qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Tc.Types qualified as GHC
import GHC.Utils.Logger qualified as GHC

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.driverPlugin = \cliOpts environment -> do
        opts <- case parsePluginOptions (removeBoilerplateOpts cliOpts) of
          Success parsed -> pure parsed
          Failure errs -> throwIO errs
        timeStage
          (GHC.hsc_logger environment)
          (opts ^. posForceTimings)
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
        logger <- GHC.getLogger
        let forceResults = opts ^. posForceTimings
            scope = GHC.moduleNameString (GHC.moduleName (GHC.tcg_mod env))
            measure stage = timeStage logger forceResults scope stage (const ())
            maybeInjectAnchors =
              if opts ^. posPreserveSourceLocations then injectAnchors else pure
        measure "source.total" $ do
          anchored <- measure "source.anchors" (maybeInjectAnchors env)
          supported <- measure "source.unsupported-markers" (injectUnsupportedMarkers anchored)
          measure "source.inlineable-pragmas" (addInlineables supported)
    , GHC.pluginRecompile = GHC.flagRecompile
    , GHC.installCoreToDos = installCorePlugin 'plinthc
    }
