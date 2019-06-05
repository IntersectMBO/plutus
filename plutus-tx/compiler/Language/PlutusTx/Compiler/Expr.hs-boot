{-# LANGUAGE FlexibleContexts  #-}

module Language.PlutusTx.Compiler.Expr (compileExpr, compileExprWithDefs, compileDataConRef) where

import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.PIRTypes

import qualified GhcPlugins                               as GHC

compileDataConRef :: Compiling m => GHC.DataCon -> m PIRTerm

compileExpr :: Compiling m => GHC.CoreExpr -> m PIRTerm

compileExprWithDefs :: Compiling m => GHC.CoreExpr -> m PIRTerm
