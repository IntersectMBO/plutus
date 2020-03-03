{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusTx.Compiler.Expr (compileExpr, compileExprWithDefs, compileDataConRef) where

import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.PIRTypes

import qualified Language.PlutusCore.Universe             as PLC

import qualified GhcPlugins                               as GHC

compileDataConRef :: Compiling uni m => GHC.DataCon -> m (PIRTerm uni)

compileExpr
    :: (Compiling uni m, PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni)
    => GHC.CoreExpr -> m (PIRTerm uni)

compileExprWithDefs
    :: (Compiling uni m, PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni)
    => GHC.CoreExpr -> m (PIRTerm uni)
