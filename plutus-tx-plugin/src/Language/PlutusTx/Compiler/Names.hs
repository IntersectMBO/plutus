{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Functions for compiling GHC names into Plutus Core names.
module Language.PlutusTx.Compiler.Names where


import                          Language.PlutusTx.Compiler.Kind
import {-# SOURCE #-}           Language.PlutusTx.Compiler.Type
import                          Language.PlutusTx.Compiler.Types
import                          Language.PlutusTx.PLCTypes

import                qualified GhcPlugins                       as GHC

import                qualified Language.PlutusCore              as PLC
import                qualified Language.PlutusCore.MkPlc        as PLC
import                          Language.PlutusCore.Quote

import                          Language.PlutusIR.Compiler.Names

import                          Data.Char
import                          Data.List
import                qualified Data.List.NonEmpty               as NE
import                qualified Data.Map                         as Map
import                qualified Data.Text                        as T

lookupName :: Scope uni fun -> GHC.Name -> Maybe (PLCVar uni fun)
lookupName (Scope ns _) n = Map.lookup n ns

{- |
Reverses the OccName tidying that GHC does, see 'tidyOccEnv'
and accompanying Notes.

This is bad, because it makes it much harder to read since the
disambiguating numbers are gone. However, these appear to be
non-deterministic (possibly depending on the order in which
modules are processed?), so we can't rely on them.

Essentially, we just strip off trailing digits.
This might remove "real" digits added by the user, but
there's not much we can do about that.

Note that this only affects the *textual* name, not the underlying
unique, so it has no effect on the behaviour of the program, merely
on how it is printed.
-}
getUntidiedOccString :: GHC.Name -> String
getUntidiedOccString n = dropWhileEnd isDigit (GHC.getOccString n)

compileNameFresh :: MonadQuote m => GHC.Name -> m PLC.Name
compileNameFresh n = safeFreshName $ T.pack $ getUntidiedOccString n

compileVarFresh :: Compiling uni fun m => GHC.Var -> m (PLCVar uni fun)
compileVarFresh v = do
    t' <- compileTypeNorm $ GHC.varType v
    n' <- compileNameFresh $ GHC.getName v
    pure $ PLC.VarDecl () n' t'

lookupTyName :: Scope uni fun -> GHC.Name -> Maybe PLCTyVar
lookupTyName (Scope _ tyns) n = Map.lookup n tyns

compileTyNameFresh :: MonadQuote m => GHC.Name -> m PLC.TyName
compileTyNameFresh n = safeFreshTyName $ T.pack $ getUntidiedOccString n

compileTyVarFresh :: Compiling uni fun m => GHC.TyVar -> m PLCTyVar
compileTyVarFresh v = do
    k' <- compileKind $ GHC.tyVarKind v
    t' <- compileTyNameFresh $ GHC.getName v
    pure $ PLC.TyVarDecl () t' k'

compileTcTyVarFresh :: Compiling uni fun m => GHC.TyCon -> m PLCTyVar
compileTcTyVarFresh tc = do
    k' <- compileKind $ GHC.tyConKind tc
    t' <- compileTyNameFresh $ GHC.getName tc
    pure $ PLC.TyVarDecl () t' k'

pushName :: GHC.Name -> PLCVar uni fun-> ScopeStack uni fun -> ScopeStack uni fun
pushName ghcName n stack = let Scope ns tyns = NE.head stack in Scope (Map.insert ghcName n ns) tyns NE.<| stack

pushNames :: [(GHC.Name, PLCVar uni fun)] -> ScopeStack uni fun -> ScopeStack uni fun
pushNames mappings stack = foldl' (\acc (n, v) -> pushName n v acc) stack mappings

pushTyName :: GHC.Name -> PLCTyVar -> ScopeStack uni fun -> ScopeStack uni fun
pushTyName ghcName n stack = let Scope ns tyns = NE.head stack in Scope ns (Map.insert ghcName n tyns) NE.<| stack

pushTyNames :: [(GHC.Name, PLCTyVar)] -> ScopeStack uni fun -> ScopeStack uni fun
pushTyNames mappings stack = foldl' (\acc (n, v) -> pushTyName n v acc) stack mappings
