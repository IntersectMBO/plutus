{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
-- | Optimization passes for removing dead code, mainly dead let bindings.
module Language.PlutusIR.Optimizer.DeadCode (removeDeadBindings) where

import           Language.PlutusIR

import qualified Language.PlutusCore      as PLC
import qualified Language.PlutusCore.Name as PLC

import           Control.Monad
import           Control.Monad.State

import           Data.Coerce
import qualified Data.IntMap              as IM

import           Lens.Micro

-- | Remove all the dead let bindings in a term.
removeDeadBindings
    :: (PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Term tyname name a
    -> Term tyname name a
removeDeadBindings t = evalState (processTerm t) mempty

type Usages = IM.IntMap Int

addUsage :: (PLC.HasUnique n unique) => n -> Usages -> Usages
addUsage n usages =
    let
        u = coerce $ n ^. PLC.unique
        old = IM.findWithDefault 0 (PLC.unUnique u) usages
    in IM.insert (PLC.unUnique u) (old+1) usages

hasUsage :: (PLC.HasUnique n unique) => n -> Usages -> Bool
hasUsage n usages =
    let
        u = coerce $ n ^. PLC.unique
    in IM.findWithDefault 0 (PLC.unUnique u) usages > 0

liveBinding
    :: (MonadState Usages m, PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Binding tyname name a
    -> m Bool
liveBinding b =
    let
        -- TODO: HasUnique instances for VarDecl and TyVarDecl?
        hasUsageVarDecl (VarDecl _ n _) = hasUsage n
        hasUsageTyVarDecl (TyVarDecl _ n _) = hasUsage n
    in case b of
        TermBind _ d _ -> gets $ hasUsageVarDecl d
        TypeBind _ d _ -> gets $ hasUsageTyVarDecl d
        DatatypeBind _ (Datatype _ d _ destr constrs) -> do
            usages <- get
            let used = hasUsageTyVarDecl d usages || hasUsage destr usages || any (\c -> hasUsageVarDecl c usages) constrs
            pure used

{- Note [Simultaneous usage analysis and dead binding elimination]
It's tempting to say that usage analysis and dead binding elmination should be
separate passes. We could proceed for each let by:
- Processing the body.
- Getting the usages for the body.
- Removing dead bindings.

But this is quadratic, because it traverses subterms many times. The problem is that
the usage information for subterms remains relevant when processing superterms, and
it is very wasteful to recompute it. Possibly there is an elegant way to separate
the code without making the computation wasteful, but for now we simply do the two
operations interleaved.

(It would be especially nice if we could move e.g. the usage analysis for types into
the Plutus Core library.)
-}

processTerm
    :: (MonadState Usages m, PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Term tyname name a
    -> m (Term tyname name a)
processTerm term = case term of
    Let x r bs t -> do
        t' <- processTerm t

        -- throw away dead bindings
        liveBindings <- case r of
            NonRec -> filterM liveBinding bs
            Rec    -> do
                -- TODO: more precise tracking of deadness of recursive bindings, probably will
                -- require a fancier algorithm or a proper dependency graph
                liveness <- traverse liveBinding bs
                -- if any binding is live assume they all are, otherwise we can
                -- safely ditch them all
                if or liveness
                then pure bs
                else pure []

        -- now handle usages and dead bindings with the bindings themselves
        processedBindings <- traverse processBinding liveBindings

        -- if we've removed all the bindings then drop the let
        if null processedBindings
        then pure t'
        else pure $ Let x r processedBindings t'
    Var x n -> do
        modify (addUsage n)
        pure $ Var x n
    TyAbs x tn k t -> TyAbs x tn k <$> processTerm t
    LamAbs x n ty t -> LamAbs x n <$> processTy ty <*> processTerm t
    Apply x t1 t2 -> Apply x <$> processTerm t1 <*> processTerm t2
    Constant x c -> pure $ Constant x c
    TyInst x t ty -> TyInst x <$> processTerm t <*> processTy ty
    Error x ty -> Error x <$> processTy ty
    Wrap x n ty t -> Wrap x n <$> processTy ty <*> processTerm t
    Unwrap x t -> Unwrap x <$> processTerm t

processVarDecl
    :: (MonadState Usages m, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => VarDecl tyname name a
    -> m (VarDecl tyname name a)
processVarDecl (VarDecl x n ty) = VarDecl x n <$> processTy ty

processTyVarDecl
    :: (MonadState Usages m)
    => TyVarDecl tyname a
    -> m (TyVarDecl tyname a)
processTyVarDecl (TyVarDecl x n k) = pure $ TyVarDecl x n k

processBinding
    :: (MonadState Usages m, PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Binding tyname name a
    -> m (Binding tyname name a)
processBinding = \case
    TermBind x d rhs -> TermBind x d <$> processTerm rhs
    TypeBind x d rhs -> TypeBind x d <$> processTy rhs
    DatatypeBind x (Datatype x' d tvs destr constrs) -> do
        dt <- Datatype x' <$> processTyVarDecl d <*> traverse processTyVarDecl tvs <*> pure destr <*> traverse processVarDecl constrs
        pure $ DatatypeBind x dt

processTy :: (MonadState Usages m, PLC.HasUnique (tyname a) PLC.TypeUnique) => Type tyname a -> m (Type tyname a)
processTy ty = case ty of
    TyVar x n -> do
        modify (addUsage n)
        pure $ TyVar x n
    TyFun x t1 t2 -> TyFun x <$> processTy t1 <*> processTy t2
    TyFix x n t -> TyFix x n <$> processTy t
    TyForall x tn k t -> TyForall x tn k <$> processTy t
    TyBuiltin x b -> pure $ TyBuiltin x b
    TyInt x n -> pure $ TyInt x n
    TyLam x n k t -> TyLam x n k <$> processTy t
    TyApp x t1 t2 -> TyApp x <$> processTy t1 <*> processTy t2
