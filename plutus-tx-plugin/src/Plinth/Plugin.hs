{-# LANGUAGE TemplateHaskellQuotes #-}

module Plinth.Plugin (plugin, plinthc) where

import PlutusTx.Plugin.Common
import PlutusTx.Plugin.Unsupported
import PlutusTx.Plugin.Utils

import Control.Monad
import GHC.Plugins qualified as GHC

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.typeCheckResultAction = \_cliOpts _modSummary ->
        injectAnchors >=> injectUnsupportedMarkers
    , GHC.pluginRecompile = GHC.flagRecompile
    , GHC.installCoreToDos = installCorePlugin 'plinthc
    }
