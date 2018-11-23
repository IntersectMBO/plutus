{-# LANGUAGE FlexibleContexts  #-}

module Language.PlutusTx.Compiler.Type where

import Language.PlutusTx.Compiler.Types
import Language.PlutusTx.PIRTypes

import qualified GhcPlugins                               as GHC

convType :: Converting m => GHC.Type -> m PIRType

getMatchInstantiated :: Converting m => GHC.Type -> m PIRTerm
