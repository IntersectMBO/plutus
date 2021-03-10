{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

-- | Functions for compiling GHC primitives into Plutus Core primitives.
module Language.PlutusTx.Compiler.Primitives where

import qualified Language.PlutusTx.Builtins          as Builtins
import           Language.PlutusTx.Compiler.Builtins
import           Language.PlutusTx.Compiler.Error
import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.Compiler.Utils
import           Language.PlutusTx.PIRTypes

import qualified GhcPlugins                          as GHC
import qualified PrimOp                              as GHC

-- These never seem to come up, rather we get the typeclass operations. Not sure if we need them.
compilePrimitiveOp :: Compiling uni fun m => GHC.PrimOp -> m (PIRTerm uni fun)
compilePrimitiveOp = \case
    GHC.IntAddOp  -> lookupBuiltinTerm 'Builtins.addInteger
    GHC.IntSubOp  -> lookupBuiltinTerm 'Builtins.subtractInteger
    GHC.IntMulOp  -> lookupBuiltinTerm 'Builtins.multiplyInteger
    -- check this one
    GHC.IntQuotOp -> lookupBuiltinTerm 'Builtins.divideInteger
    GHC.IntRemOp  -> lookupBuiltinTerm 'Builtins.remainderInteger
    GHC.IntGtOp   -> lookupBuiltinTerm 'Builtins.greaterThanInteger
    GHC.IntGeOp   -> lookupBuiltinTerm 'Builtins.greaterThanEqInteger
    GHC.IntLtOp   -> lookupBuiltinTerm 'Builtins.lessThanInteger
    GHC.IntLeOp   -> lookupBuiltinTerm 'Builtins.lessThanEqInteger
    GHC.IntEqOp   -> lookupBuiltinTerm 'Builtins.equalsInteger
    po            -> throwSd UnsupportedError $ "Primitive operation:" GHC.<+> GHC.ppr po
