{-# LANGUAGE FlexibleContexts  #-}

module PlutusTx.Compiler.Type where

import PlutusTx.Compiler.Types
import PlutusTx.PIRTypes

import qualified GhcPlugins                               as GHC

compileTypeNorm :: Compiling uni fun m => GHC.Type -> m (PIRType uni)
compileType :: Compiling uni fun m => GHC.Type -> m (PIRType uni)

getMatchInstantiated :: Compiling uni fun m => GHC.Type -> m (PIRTerm uni fun)
