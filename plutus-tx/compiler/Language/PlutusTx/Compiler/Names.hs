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
import qualified Data.Text                        as T

lookupName :: Scope -> GHC.Name -> Maybe PLCVar
lookupName (Scope ns _) n = Map.lookup n ns

compileNameFresh :: MonadQuote m => GHC.Name -> m (PLC.Name ())
compileNameFresh n = safeFreshName () $ T.pack $ GHC.getOccString n

compileVarFresh :: Compiling m => GHC.Var -> m PLCVar
compileVarFresh v = do
    t' <- compileType $ GHC.varType v
    n' <- compileNameFresh $ GHC.getName v
    pure $ PLC.VarDecl () n' t'

lookupTyName :: Scope -> GHC.Name -> Maybe PLCTyVar
lookupTyName (Scope _ tyns) n = Map.lookup n tyns

compileTyNameFresh :: MonadQuote m => GHC.Name -> m (PLC.TyName ())
compileTyNameFresh n = safeFreshTyName () $ T.pack $ GHC.getOccString n

compileTyVarFresh :: Compiling m => GHC.TyVar -> m PLCTyVar
compileTyVarFresh v = do
    k' <- compileKind $ GHC.tyVarKind v
    t' <- compileTyNameFresh $ GHC.getName v
    pure $ PLC.TyVarDecl () t' k'

compileTcTyVarFresh :: Compiling m => GHC.TyCon -> m PLCTyVar
compileTcTyVarFresh tc = do
    k' <- compileKind $ GHC.tyConKind tc
    t' <- compileTyNameFresh $ GHC.getName tc
    pure $ PLC.TyVarDecl () t' k'

pushName :: GHC.Name -> PLCVar-> ScopeStack -> ScopeStack
pushName ghcName n stack = let Scope ns tyns = NE.head stack in Scope (Map.insert ghcName n ns) tyns NE.<| stack

pushNames :: [(GHC.Name, PLCVar)] -> ScopeStack -> ScopeStack
pushNames mappings stack = foldl' (\acc (n, v) -> pushName n v acc) stack mappings

pushTyName :: GHC.Name -> PLCTyVar -> ScopeStack -> ScopeStack
pushTyName ghcName n stack = let Scope ns tyns = NE.head stack in Scope ns (Map.insert ghcName n tyns) NE.<| stack

pushTyNames :: [(GHC.Name, PLCTyVar)] -> ScopeStack -> ScopeStack
pushTyNames mappings stack = foldl' (\acc (n, v) -> pushTyName n v acc) stack mappings
