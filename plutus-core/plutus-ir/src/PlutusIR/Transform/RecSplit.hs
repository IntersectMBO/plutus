{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
module PlutusIR.Transform.RecSplit
    (recSplit) where

import qualified PlutusCore.Name                      as PLC
import           PlutusIR
import           PlutusIR.Subst

import qualified Algebra.Graph.AdjacencyMap           as AM
import qualified Algebra.Graph.AdjacencyMap.Algorithm as AM
import qualified Algebra.Graph.NonEmpty.AdjacencyMap  as AMN
import           Control.Lens
import           Data.Either
import           Data.Foldable                        (foldl')
import           Data.List                            (nub)
import qualified Data.List.NonEmpty                   as NE
import qualified Data.Map                             as M
import           Data.Semigroup.Foldable
import qualified Data.Set                             as S

{- Note [LetRec splitting pass]
This pass examines a single letrec group at a time
and maybe splits the group into sub-letgroups (rec or nonrec).

Invariants of the pass:

- Preserves the well-scopedness of the term.
- Does not turn an out-of-scope term into well-scoped.
- Does not place/move the sub-letgroups into locations other than the original letrec location (hole).
- Does not touch let-nonrec groups.

The (a) grouping into sub-letgroups
and the (b) order of appearance of these sub-groups inside the result term,
is determined by locally constructing at each reclet-group location,
a dependency graph between the bindings of the original let.

The created sub-letgroups will either be
(a) let-rec with 2 or more bindings
(b) let-nonrec with a single binding

Because of (b), it is advised to run the LetMerge pass *AFTER* this RecSplit pass, to group adjacent let-nonrecs.

This pass has the side-effect of demoting "fake" rec let-bindings into "true" nonrec let-bindings.
This gives an extra motivation to run the LetMerge pass *AFTER* this RecSplit pass.

Currently the implementation relies on 'Unique's, so there is the assumption of global uniqueness of the input term.
However, the algorithm could be changed to work without this assumption (has not been tested).
-}

{-|
Apply letrec splitting, recursively in bottom-up fashion.
-}
recSplit :: forall uni fun a name tyname.
           (Ord name, Ord tyname, PLC.HasUnique tyname PLC.TypeUnique,
            PLC.HasUnique name PLC.TermUnique)
         => Term tyname name uni fun a
         -> Term tyname name uni fun a
recSplit = transformOf termSubterms recSplitStep
  where
    recSplitStep :: Term tyname name uni fun a -> Term tyname name uni fun a
    recSplitStep = \case
        -- See Note [LetRec splitting pass]
        Let a Rec bs t ->
            let
                -- a table from principal id to the its corresponding whole let-binding
                bindingsTable :: M.Map PLC.Unique (Binding tyname name uni fun a)
                bindingsTable = M.fromList . NE.toList $ fmap (\ b -> (principal b, b)) bs
                hereSccs =
                           -- TODO: use error infrastructure
                           fromRight (error "Cycle detected in the scc-graph. This shouldn't happen in the first place.")
                           -- we take the topological sort (for the correct order)
                           -- from the SCCs (for the correct grouping) of the local dep-graph
                           . AM.topSort . AM.scc $ buildLocalDepGraph bs
            in foldl' (\ acc scc ->
                          Let a
                          (if AM.isAcyclic $ AMN.fromNonEmpty scc then NonRec else Rec)
                          (NE.fromList . M.elems . M.restrictKeys bindingsTable $ AMN.vertexSet scc)
                          acc) t hereSccs
        t  -> t


{-|
It constructs a dependency graph between the introduced bindings of the currently-examined let,
and takes
-}
buildLocalDepGraph :: forall uni fun a name tyname.
                     (Ord name, Ord tyname, PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
                   => NE.NonEmpty (Binding tyname name uni fun a) -> AM.AdjacencyMap PLC.Unique
buildLocalDepGraph bs = AM.overlays . NE.toList $ fmap bindingSubGraph bs
    where
      -- a map of a all introduced binding ids to their belonging principal id
      idTable :: M.Map PLC.Unique PLC.Unique
      idTable = foldMap1 (\ b -> M.fromList (fmap (,principal b) $ b^..bindingIds)) bs

      bindingSubGraph :: Binding tyname name uni fun a -> AM.AdjacencyMap PLC.Unique
      bindingSubGraph b =
          let freeUniques = S.map (^.PLC.theUnique) (fvBinding b)
                            -- why NonRec: if it is a datatype-binding we treat it as non-recursive
                            -- to reveal if it depends on itself,
                            -- i.e. the typeconstructor is free at the domain-part of any of its dataconstructor types
                            <> S.map (^.PLC.theUnique) (ftvBinding NonRec b)
              occursIds = M.keysSet idTable `S.intersection` freeUniques
              occursPrincipals = nub $ M.elems $ idTable `M.restrictKeys` occursIds
          in AM.connect (AM.vertex $ principal b) (AM.vertices occursPrincipals)


{-|
A function that returns a single 'Unique' for a particular binding.
We need this because let-datatypes introduce multiple identifiers,
but in our local dep. graph (buildSccs) we use a single Unique as 'the vertex' of the binding.
-}
principal :: (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
            => Binding tyname name uni fun a
            -> PLC.Unique
principal = \case TermBind _ _ (VarDecl _ n _) _                             -> n^. PLC.theUnique
                  TypeBind _ (TyVarDecl _ n _) _                             -> n ^. PLC.theUnique
                  -- arbitrary: uses the type constructor's unique as the principal unique of this data binding group
                  DatatypeBind _ (Datatype _ (TyVarDecl _ tyConstr _) _ _ _) -> tyConstr ^. PLC.theUnique
