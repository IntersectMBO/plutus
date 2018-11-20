{-# LANGUAGE FlexibleContexts  #-}

module Language.Plutus.CoreToPLC.Compiler.Type where

import Language.Plutus.CoreToPLC.Compiler.Types
import Language.Plutus.CoreToPLC.PIRTypes

import qualified GhcPlugins                               as GHC

convType :: Converting m => GHC.Type -> m PIRType

getMatchInstantiated :: Converting m => GHC.Type -> m PIRTerm
