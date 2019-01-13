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
import qualified PrelNames                           as GHC
import qualified PrimOp                              as GHC

-- These never seem to come up, rather we get the typeclass operations. Not sure if we need them.
convPrimitiveOp :: (Converting m) => GHC.PrimOp -> m PIRTerm
convPrimitiveOp = \case
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

-- Typeclasses

convEqMethod :: (Converting m) => GHC.Name -> m PIRTerm
convEqMethod name
    | name == GHC.eqName = lookupBuiltinTerm 'Builtins.equalsInteger
    | otherwise = throwSd UnsupportedError $ "Eq method:" GHC.<+> GHC.ppr name

convOrdMethod :: (Converting m) => GHC.Name -> m PIRTerm
convOrdMethod name
    -- only this one has a name defined in the lib??
    | name == GHC.geName = lookupBuiltinTerm 'Builtins.greaterThanEqInteger
    | GHC.getOccString name == ">" = lookupBuiltinTerm 'Builtins.greaterThanInteger
    | GHC.getOccString name == "<=" = lookupBuiltinTerm 'Builtins.lessThanEqInteger
    | GHC.getOccString name == "<" = lookupBuiltinTerm 'Builtins.lessThanInteger
    | otherwise = throwSd UnsupportedError $ "Ord method:" GHC.<+> GHC.ppr name

convNumMethod :: (Converting m) => GHC.Name -> m PIRTerm
convNumMethod name
    -- only this one has a name defined in the lib??
    | name == GHC.minusName = lookupBuiltinTerm 'Builtins.subtractInteger
    | GHC.getOccString name == "+" = lookupBuiltinTerm 'Builtins.addInteger
    | GHC.getOccString name == "*" = lookupBuiltinTerm 'Builtins.multiplyInteger
    | otherwise = throwSd UnsupportedError $ "Num method:" GHC.<+> GHC.ppr name

convIntegralMethod :: (Converting m) => GHC.Name -> m PIRTerm
convIntegralMethod name
    | GHC.getOccString name == "div" = lookupBuiltinTerm 'Builtins.divideInteger
    | GHC.getOccString name == "rem" = lookupBuiltinTerm 'Builtins.remainderInteger
    | otherwise = throwSd UnsupportedError $ "Integral method:" GHC.<+> GHC.ppr name
