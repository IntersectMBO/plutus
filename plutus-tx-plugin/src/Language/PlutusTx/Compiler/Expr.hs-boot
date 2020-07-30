{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusTx.Compiler.Expr (compileExpr, compileExprWithDefs, compileDataConRef) where

import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.PIRTypes

import qualified GhcPlugins                               as GHC

compileDataConRef :: Compiling uni m => GHC.DataCon -> m (PIRTerm uni)

compileExpr
    :: Compiling uni m
    => GHC.CoreExpr -> m (PIRTerm uni)

compileExprWithDefs
    :: Compiling uni m
    => GHC.CoreExpr -> m (PIRTerm uni)
