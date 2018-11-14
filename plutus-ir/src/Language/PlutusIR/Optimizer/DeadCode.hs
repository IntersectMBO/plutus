{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
-- | Optimization passes for removing dead code, mainly dead let bindings.
module Language.PlutusIR.Optimizer.DeadCode (removeDeadBindings) where

import           Language.PlutusIR
import qualified Language.PlutusIR.Analysis.Dependencies as Deps

import qualified Language.PlutusCore                     as PLC
import qualified Language.PlutusCore.Name                as PLC

import           Control.Lens
import           Control.Monad
import           Control.Monad.Reader

import           Data.Coerce
import qualified Data.Set                                as Set

import qualified Algebra.Graph                           as G
import qualified Algebra.Graph.AdjacencyMap              as AM
import qualified Algebra.Graph.ToGraph                   as T

-- | Remove all the dead let bindings in a term.
removeDeadBindings
    :: (PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Term tyname name a
    -> Term tyname name a
removeDeadBindings t =
    let
        depGraph :: G.Graph Deps.Node
        depGraph = Deps.runTermDeps t
        liveNodes :: Liveness
        liveNodes = Set.fromList $ AM.reachable Deps.Root (T.toAdjacencyMap depGraph)
    in runReader (processTerm t) liveNodes

type Liveness = Set.Set Deps.Node

live :: (MonadReader Liveness m, PLC.HasUnique n unique) => n -> m Bool
live n =
    let
        u = coerce $ n ^. PLC.unique
    in asks $ Set.member (Deps.Variable u)

liveBinding
    :: (MonadReader Liveness m, PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Binding tyname name a
    -> m Bool
liveBinding b =
    let
        -- TODO: HasUnique instances for VarDecl and TyVarDecl?
        liveVarDecl (VarDecl _ n _) = live n
        liveTyVarDecl (TyVarDecl _ n _) = live n
    in case b of
        TermBind _ d _ -> liveVarDecl d
        TypeBind _ d _ -> liveTyVarDecl d
        DatatypeBind _ (Datatype _ d _ destr constrs) -> or <$> (sequence $ [liveTyVarDecl d,  live destr] ++ fmap liveVarDecl constrs)

processTerm
    :: (MonadReader Liveness m, PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Term tyname name a
    -> m (Term tyname name a)
processTerm term = case term of
    Let x r bs t -> do
        t' <- processTerm t

        -- throw away dead bindings
        liveBindings <- filterM liveBinding bs

        -- now handle usages and dead bindings with the bindings themselves
        processedBindings <- traverse processBinding liveBindings

        -- if we've removed all the bindings then drop the let
        if null processedBindings
        then pure t'
        else pure $ Let x r processedBindings t'
    TyAbs x tn k t -> TyAbs x tn k <$> processTerm t
    LamAbs x n ty t -> LamAbs x n ty <$> processTerm t
    Apply x t1 t2 -> Apply x <$> processTerm t1 <*> processTerm t2
{- MERGE CONFLICT
    TyInst x t ty -> TyInst x <$> processTerm t <*> pure ty
    Wrap x n ty t -> Wrap x n ty <$> processTerm t
-}
    Constant x c -> pure $ Constant x c
    Builtin x bi -> pure $ Builtin x bi
    TyInst x t ty -> TyInst x <$> processTerm t <*> processTy ty
    Error x ty -> Error x <$> processTy ty
    IWrap x ty1 ty2 t -> IWrap x <$> processTy ty1 <*> processTy ty2 <*> processTerm t
    Unwrap x t -> Unwrap x <$> processTerm t
    t@Constant{} -> pure t
    t@Builtin{} -> pure t
    t@Var{} -> pure t
    t@Error{} -> pure t

processBinding
    :: (MonadReader Liveness m, PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Binding tyname name a
    -> m (Binding tyname name a)
processBinding = \case
    TermBind x d rhs -> TermBind x d <$> processTerm rhs
{- MERGE CONFLICT
    b@TypeBind{} -> pure b
    b@DatatypeBind{} -> pure b
-}
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
    TyIFix x n t -> TyIFix x n <$> processTy t
    TyForall x tn k t -> TyForall x tn k <$> processTy t
    TyBuiltin x b -> pure $ TyBuiltin x b
    TyInt x n -> pure $ TyInt x n
    TyLam x n k t -> TyLam x n k <$> processTy t
    TyApp x t1 t2 -> TyApp x <$> processTy t1 <*> processTy t2
