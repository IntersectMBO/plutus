{-# LANGUAGE FlexibleContexts  #-}

module Language.PlutusTx.Compiler.Type where

import Language.PlutusTx.Compiler.Types
import Language.PlutusTx.PIRTypes

import qualified GhcPlugins                               as GHC

compileTypeNorm :: Compiling uni fun m => GHC.Type -> m (PIRType uni)
compileType :: Compiling uni fun m => GHC.Type -> m (PIRType uni)

getMatchInstantiated :: Compiling uni fun m => GHC.Type -> m (PIRTerm uni fun)
