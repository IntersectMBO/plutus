{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Functions for compiling GHC names into Plutus Core names.
module Language.PlutusTx.Compiler.Names where


import           Language.PlutusTx.Compiler.Kind
import {-# SOURCE #-} Language.PlutusTx.Compiler.Type
import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.PLCTypes

import qualified GhcPlugins                       as GHC

import qualified Language.PlutusCore              as PLC
import qualified Language.PlutusCore.MkPlc        as PLC
import           Language.PlutusCore.Quote

import           Language.PlutusIR.Compiler.Names

import           Data.List
import qualified Data.List.NonEmpty               as NE
import qualified Data.Map                         as Map

lookupName :: Scope -> GHC.Name -> Maybe PLCVar
lookupName (Scope ns _) n = Map.lookup n ns

convNameFresh :: MonadQuote m => GHC.Name -> m (PLC.Name ())
convNameFresh n = safeFreshName () $ GHC.getOccString n

convVarFresh :: Converting m => GHC.Var -> m PLCVar
convVarFresh v = do
    t' <- convType $ GHC.varType v
    n' <- convNameFresh $ GHC.getName v
    pure $ PLC.VarDecl () n' t'

lookupTyName :: Scope -> GHC.Name -> Maybe PLCTyVar
lookupTyName (Scope _ tyns) n = Map.lookup n tyns

convTyNameFresh :: MonadQuote m => GHC.Name -> m (PLC.TyName ())
convTyNameFresh n = safeFreshTyName () $ GHC.getOccString n

convTyVarFresh :: Converting m => GHC.TyVar -> m PLCTyVar
convTyVarFresh v = do
    k' <- convKind $ GHC.tyVarKind v
    t' <- convTyNameFresh $ GHC.getName v
    pure $ PLC.TyVarDecl () t' k'

convTcTyVarFresh :: Converting m => GHC.TyCon -> m PLCTyVar
convTcTyVarFresh tc = do
    k' <- convKind $ GHC.tyConKind tc
    t' <- convTyNameFresh $ GHC.getName tc
    pure $ PLC.TyVarDecl () t' k'

pushName :: GHC.Name -> PLCVar-> ScopeStack -> ScopeStack
pushName ghcName n stack = let Scope ns tyns = NE.head stack in Scope (Map.insert ghcName n ns) tyns NE.<| stack

pushNames :: [(GHC.Name, PLCVar)] -> ScopeStack -> ScopeStack
pushNames mappings stack = foldl' (\acc (n, v) -> pushName n v acc) stack mappings

pushTyName :: GHC.Name -> PLCTyVar -> ScopeStack -> ScopeStack
pushTyName ghcName n stack = let Scope ns tyns = NE.head stack in Scope ns (Map.insert ghcName n tyns) NE.<| stack

pushTyNames :: [(GHC.Name, PLCTyVar)] -> ScopeStack -> ScopeStack
pushTyNames mappings stack = foldl' (\acc (n, v) -> pushTyName n v acc) stack mappings
