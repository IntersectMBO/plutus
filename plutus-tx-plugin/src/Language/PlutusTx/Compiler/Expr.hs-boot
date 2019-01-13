{-# LANGUAGE FlexibleContexts  #-}

module Language.PlutusTx.Compiler.Expr (convExpr, convExprWithDefs, convDataConRef) where

import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.PIRTypes

import qualified GhcPlugins                               as GHC

convDataConRef :: Converting m => GHC.DataCon -> m PIRTerm

convExpr :: Converting m => GHC.CoreExpr -> m PIRTerm

convExprWithDefs :: Converting m => GHC.CoreExpr -> m PIRTerm
