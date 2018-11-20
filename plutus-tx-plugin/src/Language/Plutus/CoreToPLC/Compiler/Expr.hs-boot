{-# LANGUAGE FlexibleContexts  #-}

module Language.Plutus.CoreToPLC.Compiler.Expr (convExpr, convExprWithDefs, convDataConRef) where

import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.PIRTypes

import qualified GhcPlugins                               as GHC

convDataConRef :: Converting m => GHC.DataCon -> m PIRTerm

convExpr :: Converting m => GHC.CoreExpr -> m PIRTerm

convExprWithDefs :: Converting m => GHC.CoreExpr -> m PIRTerm
