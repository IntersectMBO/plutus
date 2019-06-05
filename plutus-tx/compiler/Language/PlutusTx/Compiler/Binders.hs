{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Convenient functions for compiling binders.
module Language.PlutusTx.Compiler.Binders where

import           Language.PlutusTx.Compiler.Names
import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.Compiler.ValueRestriction
import           Language.PlutusTx.PIRTypes

import qualified GhcPlugins                                  as GHC

import qualified Language.PlutusIR                           as PIR

import           Control.Monad.Reader

import           Data.Traversable

-- Binder helpers

{- Note [Iterated abstraction and application]
PLC doesn't expose iterated abstraction and application.

We typically build these with a fold.
- Iterated application uses a *left* fold, since we want to apply the first variable
first.
- Iterated abstraction uses a *right* fold, since we want to bind the first
variable *last* (so it is on the outside, so will be first when applying).
-}

withVarScoped :: Compiling m => GHC.Var -> (PIR.VarDecl PIR.TyName PIR.Name () -> m a) -> m a
withVarScoped v k = do
    let ghcName = GHC.getName v
    var <- compileVarFresh v
    local (\c -> c {ccScopes=pushName ghcName var (ccScopes c)}) (k var)

withVarsScoped :: Compiling m => [GHC.Var] -> ([PIR.VarDecl PIR.TyName PIR.Name ()] -> m a) -> m a
withVarsScoped vs k = do
    vars <- for vs $ \v -> do
        let name = GHC.getName v
        var' <- compileVarFresh v
        pure (name, var')
    local (\c -> c {ccScopes=pushNames vars (ccScopes c)}) (k (fmap snd vars))

withTyVarScoped :: Compiling m => GHC.Var -> (PIR.TyVarDecl PIR.TyName () -> m a) -> m a
withTyVarScoped v k = do
    let ghcName = GHC.getName v
    var <- compileTyVarFresh v
    local (\c -> c {ccScopes=pushTyName ghcName var (ccScopes c)}) (k var)

withTyVarsScoped :: Compiling m => [GHC.Var] -> ([PIR.TyVarDecl PIR.TyName ()] -> m a) -> m a
withTyVarsScoped vs k = do
    vars <- for vs $ \v -> do
        let name = GHC.getName v
        var' <- compileTyVarFresh v
        pure (name, var')
    local (\c -> c {ccScopes=pushTyNames vars (ccScopes c)}) (k (fmap snd vars))

-- | Builds a lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkLamAbsScoped :: Compiling m => GHC.Var -> m PIRTerm -> m PIRTerm
mkLamAbsScoped v body = withVarScoped v $ \(PIR.VarDecl _ n t) -> PIR.LamAbs () n t <$> body

mkIterLamAbsScoped :: Compiling m => [GHC.Var] -> m PIRTerm -> m PIRTerm
mkIterLamAbsScoped vars body = foldr (\v acc -> mkLamAbsScoped v acc) body vars

-- | Builds a type abstraction, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyAbsScoped :: Compiling m => GHC.Var -> m PIRTerm -> m PIRTerm
mkTyAbsScoped v body = withTyVarScoped v $ \(PIR.TyVarDecl _ t k) -> do
    body' <- body
    checkTyAbsBody body'
    pure $ PIR.TyAbs () t k body'

mkIterTyAbsScoped :: Compiling m => [GHC.Var] -> m PIRTerm -> m PIRTerm
mkIterTyAbsScoped vars body = foldr (\v acc -> mkTyAbsScoped v acc) body vars

-- | Builds a forall, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyForallScoped :: Compiling m => GHC.Var -> m PIRType -> m PIRType
mkTyForallScoped v body = withTyVarScoped v $ \(PIR.TyVarDecl _ t k) -> PIR.TyForall () t k <$> body

mkIterTyForallScoped :: Compiling m => [GHC.Var] -> m PIRType -> m PIRType
mkIterTyForallScoped vars body = foldr (\v acc -> mkTyForallScoped v acc) body vars

-- | Builds a type lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyLamScoped :: Compiling m => GHC.Var -> m PIRType -> m PIRType
mkTyLamScoped v body = withTyVarScoped v $ \(PIR.TyVarDecl _ t k) -> PIR.TyLam () t k <$> body

mkIterTyLamScoped :: Compiling m => [GHC.Var] -> m PIRType -> m PIRType
mkIterTyLamScoped vars body = foldr (\v acc -> mkTyLamScoped v acc) body vars
