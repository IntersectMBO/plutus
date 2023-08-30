-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

-- | Convenient functions for compiling binders.
module PlutusTx.Compiler.Binders where

import PlutusTx.Compiler.Names
import PlutusTx.Compiler.Types
import PlutusTx.PIRTypes

import GHC.Plugins qualified as GHC

import PlutusIR qualified as PIR

import Control.Monad.Reader

import Data.Traversable

-- Binder helpers

{- Note [Iterated abstraction and application]
PLC doesn't expose iterated abstraction and application.

We typically build these with a fold.
- Iterated application uses a *left* fold, since we want to apply the first variable
first.
- Iterated abstraction uses a *right* fold, since we want to bind the first
variable *last* (so it is on the outside, so will be first when applying).
-}

withVarScoped ::
    CompilingDefault uni fun m ann =>
    GHC.Var ->
    (PIR.VarDecl PIR.TyName PIR.Name uni Ann -> m a) ->
    m a
withVarScoped v k = do
    let ghcName = GHC.getName v
    var <- compileVarFresh annMayInline v
    local (\c -> c {ccScope=pushName ghcName var (ccScope c)}) (k var)

-- | Like `withVarScoped`, but takes a `PIRType`, and uses it for the type
-- of the compiled `GHC.Var`.
withVarTyScoped ::
    CompilingDefault uni fun m ann =>
    GHC.Var ->
    PIRType uni ->
    (PIR.VarDecl PIR.TyName PIR.Name uni Ann -> m a) ->
    m a
withVarTyScoped v t k = do
    let ghcName = GHC.getName v
    var <- compileVarWithTyFresh annMayInline v t
    local (\c -> c {ccScope=pushName ghcName var (ccScope c)}) (k var)

withVarsScoped ::
    CompilingDefault uni fun m ann =>
    [GHC.Var] ->
    ([PIR.VarDecl PIR.TyName PIR.Name uni Ann] -> m a) ->
    m a
withVarsScoped vs k = do
    vars <- for vs $ \v -> do
        let name = GHC.getName v
        var' <- compileVarFresh annMayInline v
        pure (name, var')
    local (\c -> c {ccScope=pushNames vars (ccScope c)}) (k (fmap snd vars))

withTyVarScoped ::
    Compiling uni fun m ann =>
    GHC.Var ->
    (PIR.TyVarDecl PIR.TyName Ann -> m a) ->
    m a
withTyVarScoped v k = do
    let ghcName = GHC.getName v
    var <- compileTyVarFresh v
    local (\c -> c {ccScope=pushTyName ghcName var (ccScope c)}) (k var)

withTyVarsScoped ::
    Compiling uni fun m ann =>
    [GHC.Var] ->
    ([PIR.TyVarDecl PIR.TyName Ann] -> m a) ->
    m a
withTyVarsScoped vs k = do
    vars <- for vs $ \v -> do
        let name = GHC.getName v
        var' <- compileTyVarFresh v
        pure (name, var')
    local (\c -> c {ccScope=pushTyNames vars (ccScope c)}) (k (fmap snd vars))

-- | Builds a lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkLamAbsScoped ::
    CompilingDefault uni fun m ann =>
    GHC.Var ->
    m (PIRTerm uni fun) ->
    m (PIRTerm uni fun)
mkLamAbsScoped v body = withVarScoped v $ \(PIR.VarDecl _ n t) -> PIR.LamAbs annMayInline n t <$> body

mkIterLamAbsScoped :: CompilingDefault uni fun m ann => [GHC.Var] -> m (PIRTerm uni fun) -> m (PIRTerm uni fun)
mkIterLamAbsScoped vars body = foldr (\v acc -> mkLamAbsScoped v acc) body vars

-- | Builds a type abstraction, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyAbsScoped :: Compiling uni fun m ann => GHC.Var -> m (PIRTerm uni fun) -> m (PIRTerm uni fun)
mkTyAbsScoped v body = withTyVarScoped v $ \(PIR.TyVarDecl _ t k) -> PIR.TyAbs annMayInline t k <$> body

mkIterTyAbsScoped :: Compiling uni fun m ann => [GHC.Var] -> m (PIRTerm uni fun) -> m (PIRTerm uni fun)
mkIterTyAbsScoped vars body = foldr (\v acc -> mkTyAbsScoped v acc) body vars

-- | Builds a forall, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyForallScoped :: Compiling uni fun m ann => GHC.Var -> m (PIRType uni) -> m (PIRType uni)
mkTyForallScoped v body =
    withTyVarScoped v $ \(PIR.TyVarDecl _ t k) -> PIR.TyForall annMayInline t k <$> body

mkIterTyForallScoped :: Compiling uni fun m ann => [GHC.Var] -> m (PIRType uni) -> m (PIRType uni)
mkIterTyForallScoped vars body = foldr (\v acc -> mkTyForallScoped v acc) body vars

-- | Builds a type lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyLamScoped :: Compiling uni fun m ann => GHC.Var -> m (PIRType uni) -> m (PIRType uni)
mkTyLamScoped v body =
    withTyVarScoped v $ \(PIR.TyVarDecl _ t k) -> PIR.TyLam annMayInline t k <$> body

mkIterTyLamScoped :: Compiling uni fun m ann => [GHC.Var] -> m (PIRType uni) -> m (PIRType uni)
mkIterTyLamScoped vars body = foldr (\v acc -> mkTyLamScoped v acc) body vars
