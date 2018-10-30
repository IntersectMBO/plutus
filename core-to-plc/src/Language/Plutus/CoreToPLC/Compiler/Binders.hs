{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Convenient functions for compiling binders.
module Language.Plutus.CoreToPLC.Compiler.Binders where

import           Language.Plutus.CoreToPLC.Compiler.Names
import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.Compiler.ValueRestriction
import           Language.Plutus.CoreToPLC.PLCTypes

import qualified GhcPlugins                                          as GHC

import qualified Language.PlutusCore                                 as PLC

import           Control.Monad.Reader

-- Binder helpers

{- Note [Iterated abstraction and application]
PLC doesn't expose iterated abstraction and application.

We typically build these with a fold.
- Iterated application uses a *left* fold, since we want to apply the first variable
first.
- Iterated abstraction uses a *right* fold, since we want to bind the first
variable *last* (so it is on the outside, so will be first when applying).
-}

-- | Builds a lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkLamAbsScoped :: Converting m => GHC.Var -> m PLCTerm -> m PLCTerm
mkLamAbsScoped v body = do
    let ghcName = GHC.getName v
    var@(PLCVar n' t') <- convVarFresh v
    body' <- local (\c -> c {ccScopes=pushName ghcName var (ccScopes c)}) body
    pure $ PLC.LamAbs () n' t' body'

mkIterLamAbsScoped :: Converting m => [GHC.Var] -> m PLCTerm -> m PLCTerm
mkIterLamAbsScoped vars body = foldr (\v acc -> mkLamAbsScoped v acc) body vars

-- | Builds a type abstraction, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyAbsScoped :: Converting m => GHC.Var -> m PLCTerm -> m PLCTerm
mkTyAbsScoped v body = do
    let ghcName = GHC.getName v
    var@(PLCTyVar t' k') <- convTyVarFresh v
    body' <- local (\c -> c {ccScopes=pushTyName ghcName var (ccScopes c)}) body
    checkTyAbsBody body'
    pure $ PLC.TyAbs () t' k' body'

mkIterTyAbsScoped :: Converting m => [GHC.Var] -> m PLCTerm -> m PLCTerm
mkIterTyAbsScoped vars body = foldr (\v acc -> mkTyAbsScoped v acc) body vars

-- | Builds a forall, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyForallScoped :: Converting m => GHC.Var -> m PLCType -> m PLCType
mkTyForallScoped v body = do
    let ghcName = GHC.getName v
    var@(PLCTyVar t' k') <- convTyVarFresh v
    body' <- local (\c -> c {ccScopes=pushTyName ghcName var (ccScopes c)}) body
    pure $ PLC.TyForall () t' k' body'

mkIterTyForallScoped :: Converting m => [GHC.Var] -> m PLCType -> m PLCType
mkIterTyForallScoped vars body = foldr (\v acc -> mkTyForallScoped v acc) body vars

-- | Builds a type lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyLamScoped :: Converting m => GHC.Var -> m PLCType -> m PLCType
mkTyLamScoped v body = do
    let ghcName = GHC.getName v
    var@(PLCTyVar t' k') <- convTyVarFresh v
    body' <- local (\c -> c {ccScopes=pushTyName ghcName var (ccScopes c)}) body
    pure $ PLC.TyLam () t' k' body'

mkIterTyLamScoped :: Converting m => [GHC.Var] -> m PLCType -> m PLCType
mkIterTyLamScoped vars body = foldr (\v acc -> mkTyLamScoped v acc) body vars
