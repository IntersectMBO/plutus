{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusTx.Compiler.Expr (compileExpr, compileExprWithDefs, compileDataConRef) where

import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.PIRTypes

import qualified GhcPlugins                               as GHC

compileDataConRef :: Compiling uni fun m => GHC.DataCon -> m (PIRTerm uni fun)

compileExpr
    :: CompilingDefault uni fun m
    => GHC.CoreExpr -> m (PIRTerm uni fun)

compileExprWithDefs
    :: CompilingDefault uni fun m
    => GHC.CoreExpr -> m (PIRTerm uni fun)
