{-# LANGUAGE FlexibleContexts  #-}

module Language.Plutus.CoreToPLC.Compiler.Expr (convExpr, convExprWithDefs) where

import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.PLCTypes

import qualified GhcPlugins                               as GHC

convExpr :: Converting m => GHC.CoreExpr -> m PLCTerm

convExprWithDefs :: Converting m => GHC.CoreExpr -> m PLCTerm
