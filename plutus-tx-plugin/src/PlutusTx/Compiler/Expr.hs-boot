{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusTx.Compiler.Expr (compileExpr, compileExprWithDefs, compileDataConRef) where

import           PlutusTx.Compiler.Types
import           PlutusTx.PIRTypes

import qualified GhcPlugins                               as GHC

compileDataConRef :: Compiling uni fun m => GHC.DataCon -> m (PIRTerm uni fun)

compileExpr
    :: CompilingDefault uni fun m
    => GHC.CoreExpr -> m (PIRTerm uni fun)

compileExprWithDefs
    :: CompilingDefault uni fun m
    => GHC.CoreExpr -> m (PIRTerm uni fun)
