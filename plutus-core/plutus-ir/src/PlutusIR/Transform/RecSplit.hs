-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module PlutusIR.Transform.RecSplit (recSplit, recSplitPass) where

import PlutusCore.Name.Unique qualified as PLC
import PlutusIR
import PlutusIR.Subst

import Algebra.Graph.AdjacencyMap qualified as AM
import Algebra.Graph.AdjacencyMap.Algorithm qualified as AM hiding (isAcyclic)
import Algebra.Graph.NonEmpty.AdjacencyMap qualified as AMN
import Algebra.Graph.ToGraph (isAcyclic)
import Control.Lens
import Data.Either
import Data.Foldable qualified as Foldable (foldl')
import Data.List (nub)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Semigroup.Foldable
import Data.Set qualified as S
import Data.Set.Lens (setOf)
import PlutusCore qualified as PLC
import PlutusIR.MkPir (mkLet)
import PlutusIR.Pass
import PlutusIR.TypeCheck qualified as TC
import PlutusPrelude ((<^>))

{- Note [LetRec splitting pass]

This pass can achieve two things:

- turn recursive let-bindings which are not really recursive into non-recursive let-bindings.
- break down letrec groups into smaller ones, based on the dependencies of the group's bindings.

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

Currently the implementation relies on 'Unique's, so there is the assumption of global uniqueness of the input term.
However, the algorithm could be changed to work without this assumption (has not been tested).
-}

{- Note [Principal id]
The algorihtm identifies & stores bindings and their corresponding rhs'es in some intermediate tables.
To identify/store each binding to such tables, we need to "key" them by a single unique identifier.

For term bindings and type bindings this is easily achieved by using the single introduced name or tyname as "the key" (principal id).

Datatype bindings, however, introduce multiple names and tynames (i.e. type-constructor, type args, destructor, data-constructors)
and the 'principal' function arbitrarily chooses between one of these introduced names/tynames of the databind
to represent the "principal" id of the whole datatype binding so it can be used as "the key".
-}

recSplitPass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, Applicative m)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
recSplitPass tcconfig = simplePass "recursive let split" tcconfig recSplit

{-|
Apply letrec splitting, recursively in bottom-up fashion. -}
recSplit
  :: forall uni fun a name tyname
   . (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
  => Term tyname name uni fun a
  -> Term tyname name uni fun a
recSplit = transformOf termSubterms recSplitStep

{-|
Apply splitting for a single letrec group. -}
recSplitStep
  :: forall uni fun a name tyname
   . (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
  => Term tyname name uni fun a -> Term tyname name uni fun a
recSplitStep = \case
  -- See Note [LetRec splitting pass]
  Let a Rec bs t ->
    let
      -- a table from principal id to the its corresponding 'Binding'
      bindingsTable :: M.Map PLC.Unique (Binding tyname name uni fun a)
      bindingsTable = M.fromList . NE.toList $ fmap (\b -> (principal b, b)) bs
      hereSccs =
        fromRight (error "Cycle detected in the scc-graph. This shouldn't happen in the first place.")
          -- we take the topological sort (for the correct order)
          -- from the SCCs (for the correct grouping) of the local dep-graph
          . AM.topSort
          . AM.scc
          $ buildLocalDepGraph bs

      genLetFromScc acc scc =
        mkLet
          a
          (if isAcyclic scc then NonRec else Rec)
          (M.elems . M.restrictKeys bindingsTable $ AMN.vertexSet scc)
          acc
     in
      Foldable.foldl' genLetFromScc t hereSccs
  t -> t

{-|
It constructs a dependency graph for the currently-examined let-group.

The vertices of this graph are the bindings of this let-group, and the edges,
dependencies between those bindings.

This local graph may contain loops:
- A "self-edge" indicates a self-recursive binding.
- Any other loop indicates mutual-recursive bindings. -}
buildLocalDepGraph
  :: forall uni fun a name tyname
   . (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
  => NE.NonEmpty (Binding tyname name uni fun a) -> AM.AdjacencyMap PLC.Unique
buildLocalDepGraph bs =
  -- join together
  AM.overlays . NE.toList $ fmap bindingSubGraph bs
  where
    -- a map of a all introduced binding ids of this letgroup to their belonging principal id
    idTable :: M.Map PLC.Unique PLC.Unique
    idTable = foldMap1 (\b -> M.fromList (fmap (,principal b) $ b ^.. bindingIds)) bs

    -- Given a binding, it intersects the free uniques of the binding,
    -- with the introduced uniques of the current let group (all bindings).
    -- The result of this intersection is the "local" dependencies of the binding to other
    -- "sibling" bindings of this let group or to itself (if self-recursive).
    -- It returns a graph which connects this binding to all of its calculated "local" dependencies.
    bindingSubGraph :: Binding tyname name uni fun a -> AM.AdjacencyMap PLC.Unique
    bindingSubGraph b =
      -- the free uniques (variables or tyvariables) that occur inside this binding
      -- Special case for datatype bindings:
      -- To find out if the binding is self-recursive,
      -- we treat it like it was originally belonging to a let-nonrec (`ftvBinding NonRec`).
      -- Then, if it the datatype is indeed self-recursive, the call to `ftvBinding NonRec` will return
      -- its typeconstructor as free.
      let freeUniques = setOf (fvBinding . PLC.theUnique <^> ftvBinding NonRec . PLC.theUnique) b
          -- the "local" dependencies
          occursIds = M.keysSet idTable `S.intersection` freeUniques
          -- maps the ids of the "local" dependencies to their principal uniques.
          -- See Note [Principal id]
          occursPrincipals = nub $ M.elems $ idTable `M.restrictKeys` occursIds
       in AM.connect (AM.vertex $ principal b) (AM.vertices occursPrincipals)

{-|
A function that returns a single 'Unique' for a particular binding.
See Note [Principal id] -}
principal
  :: (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
  => Binding tyname name uni fun a
  -> PLC.Unique
principal = \case
  TermBind _ _ (VarDecl _ n _) _ -> n ^. PLC.theUnique
  TypeBind _ (TyVarDecl _ n _) _ -> n ^. PLC.theUnique
  -- arbitrary: uses the type constructor's unique as the principal unique of this data binding group
  DatatypeBind _ (Datatype _ (TyVarDecl _ tyConstr _) _ _ _) -> tyConstr ^. PLC.theUnique
