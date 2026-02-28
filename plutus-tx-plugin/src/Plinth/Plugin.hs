{-# LANGUAGE TemplateHaskellQuotes #-}

module Plinth.Plugin (plugin, plinthc) where

import PlutusTx.Plugin.Common
import PlutusTx.Plugin.Utils

import GHC.Plugins qualified as GHC

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.typeCheckResultAction = injectAnchors
    , GHC.pluginRecompile = GHC.flagRecompile
    , GHC.installCoreToDos = installCorePlugin 'plinthc
    }
