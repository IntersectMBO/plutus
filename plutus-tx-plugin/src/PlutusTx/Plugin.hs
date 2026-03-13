{-# LANGUAGE TemplateHaskellQuotes #-}

module PlutusTx.Plugin (plugin, plc) where

import PlutusTx.Plugin.Common
import PlutusTx.Plugin.Unsupported
import PlutusTx.Plugin.Utils

import GHC.Plugins qualified as GHC

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.typeCheckResultAction = \_cliOpts _modSummary -> injectUnsupportedMarkers
    , GHC.pluginRecompile = GHC.flagRecompile
    , GHC.installCoreToDos = installCorePlugin 'plc
    }
