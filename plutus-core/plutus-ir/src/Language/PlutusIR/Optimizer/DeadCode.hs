{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeOperators    #-}
-- | Optimization passes for removing dead code, mainly dead let bindings.
module Language.PlutusIR.Optimizer.DeadCode (removeDeadBindings) where

import           Language.PlutusIR
import qualified Language.PlutusIR.Analysis.Dependencies as Deps
import           Language.PlutusIR.MkPir
import           Language.PlutusIR.Transform.Rename      ()

import qualified Language.PlutusCore                     as PLC
import qualified Language.PlutusCore.Constant            as PLC
import qualified Language.PlutusCore.Name                as PLC

import           Control.Lens
import           Control.Monad
import           Control.Monad.Reader

import           Data.Coerce
import qualified Data.Set                                as Set

import qualified Algebra.Graph                           as G
import qualified Algebra.Graph.ToGraph                   as T
import qualified Data.List.NonEmpty                      as NE

-- | Remove all the dead let bindings in a term.
removeDeadBindings
    :: (PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique,
       PLC.ToBuiltinMeaning uni fun)
    => Term tyname name uni fun a
    -> Term tyname name uni fun a
removeDeadBindings t =
    let tRen = PLC.runQuote $ PLC.rename t
    in runReader (transformMOf termSubterms processTerm tRen) (calculateLiveness tRen)

type Liveness = Set.Set Deps.Node

calculateLiveness
    :: (PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique,
       PLC.ToBuiltinMeaning uni fun)
    => Term tyname name uni fun a
    -> Liveness
calculateLiveness t =
    let
        depGraph :: G.Graph Deps.Node
        depGraph = fst $ Deps.runTermDeps t
    in Set.fromList $ T.reachable Deps.Root depGraph

live :: (MonadReader Liveness m, PLC.HasUnique n unique) => n -> m Bool
live n =
    let
        u = coerce $ n ^. PLC.unique
    in asks $ Set.member (Deps.Variable u)

liveBinding
    :: (MonadReader Liveness m, PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
    => Binding tyname name uni fun a
    -> m Bool
liveBinding =
    let
        -- TODO: HasUnique instances for VarDecl and TyVarDecl?
        liveVarDecl (VarDecl _ n _) = live n
        liveTyVarDecl (TyVarDecl _ n _) = live n
    in \case
        TermBind _ _ d _ -> liveVarDecl d
        TypeBind _ d _ -> liveTyVarDecl d
        DatatypeBind _ (Datatype _ d _ destr constrs) -> or <$> (sequence $ [liveTyVarDecl d,  live destr] ++ fmap liveVarDecl constrs)

processTerm
    :: (MonadReader Liveness m, PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
    => Term tyname name uni fun a
    -> m (Term tyname name uni fun a)
processTerm = \case
    -- throw away dead bindings
    Let x r bs t -> mkLet x r <$> filterM liveBinding (NE.toList bs) <*> pure t
    x            -> pure x
