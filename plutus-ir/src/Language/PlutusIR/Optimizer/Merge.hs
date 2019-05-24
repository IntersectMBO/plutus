{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
-- | Optimization passes for merging independent let-bindings together.
module Language.PlutusIR.Optimizer.Merge (mergeLets) where

import           Language.PlutusIR
import qualified Language.PlutusIR.Analysis.Dependencies as Deps
import           Language.PlutusIR.MkPir

import qualified Language.PlutusCore                     as PLC
import qualified Language.PlutusCore.Name                as PLC

import           Control.Lens
import           Control.Monad.Reader

import           Data.List
import           Data.Maybe
import qualified Data.Set                                as Set

import qualified Algebra.Graph                           as G
import qualified Algebra.Graph.ToGraph                   as T

import Debug.Trace

mergeLets
    :: (PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Term tyname name a
    -> Term tyname name a
mergeLets t =
    let
        depGraph :: G.Graph Deps.Node
        depGraph = Deps.runTermDeps t
    in
        runReader (transformMOf termSubterms mergeTerm t) depGraph

{- Note [Merging lets]
We can merge independent, non-recursive, let bindings together into a single let binding, which is
nice since it reduces the nesting of the program.

We can *nearly* do this by just looking at the dependency graph and constructing level sets. However,
nodes in the same level set may not be mergeable if their let bindings are not adjacent.

So as it stands we need to traverse the term manually, performing local merging.
-}
mergeTerm
    :: (MonadReader (G.Graph Deps.Node) m, PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Term tyname name a
    -> m (Term tyname name a)
mergeTerm = \case
    Let x NonRec bs (Let x' NonRec bs' t) -> do
        deps <- ask
        let dependents :: Set.Set PLC.Unique
            dependents = Set.fromList $ do
                b <- bs
                u <- bindingUniques b
                {-
                Look for the nodes which depend on the bindings defined in this let.

                Logically this should be the *reachable* set. However, given that we're already topologically
                ordered, the only way there can be a transitive dependency between two adjacent nodes is if
                there is a direct dependency. To see this, suppose that there were a transitive dependency
                A -> B -> C, but A and C are adjacent. This is impossible, since B must come between A and C
                in a topological ordering.
                -}
                mapMaybe Deps.nodeUnique $ Set.toList $ T.preSet (Deps.Variable u) deps

        let (mergeable, nonMergeable) = partition (\b -> (Set.fromList $ bindingUniques b) `Set.disjoint` dependents) bs'
        --let msg = "Unsafe: " <> show dependents <> " Mergeable: " <> show (mergeable >>= bindingUniques) <> " Unmergeable: " <> show (nonMergeable >>= bindingUniques)

        pure $ mkLet x NonRec (bs ++ mergeable) (mkLet x' NonRec nonMergeable t)
    x -> pure x

bindingUniques
    :: (PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Binding tyname name a
    -> [PLC.Unique]
bindingUniques = \case
    TermBind _ (VarDecl _ n _) _ -> [n ^. PLC.unique . coerced]
    TypeBind _ (TyVarDecl _ n _) _ -> [n ^. PLC.unique . coerced]
    DatatypeBind _ (Datatype _ d tvs destr constrs) ->
        let
            tyus = fmap (\n -> n ^. PLC.unique . coerced) $ tyVarDeclName d : fmap tyVarDeclName tvs
            tus = fmap (\n -> n ^. PLC.unique . coerced) $ destr : fmap varDeclName constrs
        in tyus ++ tus
