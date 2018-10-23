{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Functions for compiling GHC primitives into Plutus Core primitives.
module Language.Plutus.CoreToPLC.Compiler.Primitives where

import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.Compiler.Utils
import           Language.Plutus.CoreToPLC.Error
import           Language.Plutus.CoreToPLC.PLCTypes
import           Language.Plutus.CoreToPLC.Utils

import qualified Language.PlutusCore                      as PLC

import qualified GhcPlugins                               as GHC
import qualified PrelNames                                as GHC
import qualified PrimOp                                   as GHC

-- These never seem to come up, rather we get the typeclass operations. Not sure if we need them.
convPrimitiveOp :: (Converting m) => GHC.PrimOp -> m PLCTerm
convPrimitiveOp = \case
    GHC.IntAddOp  -> pure $ mkIntFun PLC.AddInteger
    GHC.IntSubOp  -> pure $ mkIntFun PLC.SubtractInteger
    GHC.IntMulOp  -> pure $ mkIntFun PLC.MultiplyInteger
    -- check this one
    GHC.IntQuotOp -> pure $ mkIntFun PLC.DivideInteger
    GHC.IntRemOp  -> pure $ mkIntFun PLC.RemainderInteger
    GHC.IntGtOp   -> pure $ mkIntRel PLC.GreaterThanInteger
    GHC.IntGeOp   -> pure $ mkIntRel PLC.GreaterThanEqInteger
    GHC.IntLtOp   -> pure $ mkIntRel PLC.LessThanInteger
    GHC.IntLeOp   -> pure $ mkIntRel PLC.LessThanEqInteger
    GHC.IntEqOp   -> pure $ mkIntRel PLC.EqInteger
    po            -> throwSd UnsupportedError $ "Primitive operation:" GHC.<+> GHC.ppr po

-- Typeclasses

convEqMethod :: (Converting m) => GHC.Name -> m PLCTerm
convEqMethod name
    | name == GHC.eqName = pure $ mkIntRel PLC.EqInteger
    | otherwise = throwSd UnsupportedError $ "Eq method:" GHC.<+> GHC.ppr name

convOrdMethod :: (Converting m) => GHC.Name -> m PLCTerm
convOrdMethod name
    -- only this one has a name defined in the lib??
    | name == GHC.geName = pure $ mkIntRel PLC.GreaterThanEqInteger
    | GHC.getOccString name == ">" = pure $ mkIntRel PLC.GreaterThanInteger
    | GHC.getOccString name == "<=" = pure $ mkIntRel PLC.LessThanEqInteger
    | GHC.getOccString name == "<" = pure $ mkIntRel PLC.LessThanInteger
    | otherwise = throwSd UnsupportedError $ "Ord method:" GHC.<+> GHC.ppr name

convNumMethod :: (Converting m) => GHC.Name -> m PLCTerm
convNumMethod name
    -- only this one has a name defined in the lib??
    | name == GHC.minusName = pure $ mkIntFun PLC.SubtractInteger
    | GHC.getOccString name == "+" = pure $ mkIntFun PLC.AddInteger
    | GHC.getOccString name == "*" = pure $ mkIntFun PLC.MultiplyInteger
    | otherwise = throwSd UnsupportedError $ "Num method:" GHC.<+> GHC.ppr name
