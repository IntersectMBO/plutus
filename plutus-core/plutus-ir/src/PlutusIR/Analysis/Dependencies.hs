{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}

{- | Functions for computing the dependency graph of variables within a term or type.
A "dependency" between two nodes "A depends on B" means that B cannot be removed
from the program without also removing A.
-}
module PlutusIR.Analysis.Dependencies (
  Node (..),
  DepGraph,
  runTermDeps,
) where

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name qualified as PLC

import PlutusIR
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.Purity

import Control.Lens hiding (Strict)
import Control.Monad.Reader

import Algebra.Graph.Class qualified as G
import Data.Set qualified as Set

import Data.List.NonEmpty qualified as NE

import PlutusIR.Analysis.Builtins
import PlutusIR.Analysis.VarInfo

{- | A node in a dependency graph. Either a specific 'PLC.Unique', or a specific
node indicating the root of the graph. We need the root node because when computing the
dependency graph of, say, a term, there will not be a binding for the term itself which
we can use to represent it in the graph.
-}
data Node = Variable PLC.Unique | Root deriving stock (Show, Eq, Ord)

data DepCtx tyname name uni fun = DepCtx
  { _depNode         :: Node
  , _depBuiltinsInfo :: BuiltinsInfo uni fun
  , _depVarInfo      :: VarsInfo tyname name
  }
makeLenses ''DepCtx

{- | A constraint requiring @g@ to be a 'G.Graph' (so we can compute e.g. a @Relation@ from
it), whose vertices are 'Node's.
-}
type DepGraph g = (G.Graph g, G.Vertex g ~ Node)

{- | Compute the dependency graph of a 'Term'. The 'Root' node will correspond to the term itself.

For example, the graph of @[(let (nonrec) (vardecl x t) y) [x z]]@ is
@
    ROOT -> x
    ROOT -> z
    x -> y
    x -> t
@
-}
runTermDeps ::
  ( DepGraph g
  , PLC.HasUnique tyname PLC.TypeUnique
  , PLC.HasUnique name PLC.TermUnique
  , PLC.ToBuiltinMeaning uni fun
  ) =>
  BuiltinsInfo uni fun ->
  VarsInfo tyname name ->
  Term tyname name uni fun a ->
  g
runTermDeps binfo vinfo t = flip runReader (DepCtx Root binfo vinfo) $ termDeps t

-- | Record some dependencies on the current node.
currentDependsOn ::
  (DepGraph g, MonadReader (DepCtx tyname name uni fun) m) =>
  [PLC.Unique] ->
  m g
currentDependsOn us = do
  current <- view depNode
  pure $ G.connect (G.vertices [current]) (G.vertices (fmap Variable us))

-- | Process the given action with the given name as the current node.
withCurrent ::
  (MonadReader (DepCtx tyname name uni fun) m, PLC.HasUnique n u) =>
  n ->
  m g ->
  m g
withCurrent n = local $ set depNode $ Variable $ n ^. PLC.theUnique

{- Note [Strict term bindings and dependencies]
A node inside a strict let binding can incur a dependency on it even if the defined variable
is unused.

Consider:

let strict x = error in y

This evaluates to error, because the RHS of a strict binding is evaluated when we evaluate
the let-term.

We only care about this for its *effects*: the variable itself is still unused. So we only need to
worry in the case where the RHS is not a value. If it *is* a value, then evaluating it is a noop,
so there can be no effects that we're missing. Essentially we are using "is a value" as an
under-approximation of "is pure".

From the point of view of our algorithm, we handle the dependency by treating it as though
there was an reference to the newly bound variable alongside the binding, but only in the
cases where it matters.
-}

{- Note [Dependencies for datatype bindings, and pruning them]
At face value, all the names introduced by datatype bindings should depend on each other.
Given our meaning of "A depends on B", since we cannot remove any part of the datatype
binding without removing the whole thing, they all depend on each other

However, there are some circumstances in which we *can* prune datatype bindings.

In particular, if the datatype is only used at the type-level (i.e. all the term-level parts
(constructors and destructor) are dead), then we are free to completely replace the binding
with one for a trivial type with the same kind.

This is because there are *no* term-level effects, and types are erased in the end, so
in this case rest of the datatype binding really is superfluous.

But how do we represent this in the dependency graph? We still need to have proper dependencies
so that we don't make the wrong decisions wrt transitively used values, e.g.

let U :: * = ...
let datatype T = T1 | T2 U
in T1

Here we need to not delete U, even though T2 is "dead"!

The solution is to focus on the meaning of "dependency": with the pruning that we can do, we *can*
remove all the term level bits en masse, but only en-mass. So we need to make *them* into a clique,
so that this is visible to the dependency analysis.
-}

bindingDeps ::
  ( DepGraph g
  , MonadReader (DepCtx tyname name uni fun) m
  , PLC.HasUnique tyname PLC.TypeUnique
  , PLC.HasUnique name PLC.TermUnique
  , PLC.ToBuiltinMeaning uni fun
  ) =>
  Binding tyname name uni fun a ->
  m g
bindingDeps b = case b of
  TermBind _ strictness d@(VarDecl _ n _) rhs -> do
    vDeps <- varDeclDeps d
    tDeps <- withCurrent n $ termDeps rhs

    binfo <- view depBuiltinsInfo
    -- See Note [Strict term bindings and dependencies]
    vinfo <- view depVarInfo
    evalDeps <- case strictness of
      Strict | not (isPure binfo vinfo rhs) -> currentDependsOn [n ^. PLC.theUnique]
      _                                     -> pure G.empty

    pure $ G.overlays [vDeps, tDeps, evalDeps]
  TypeBind _ d@(TyVarDecl _ n _) rhs -> do
    vDeps <- tyVarDeclDeps d
    tDeps <- withCurrent n $ typeDeps rhs
    pure $ G.overlay vDeps tDeps
  DatatypeBind _ (Datatype _ d tvs destr constrs) -> do
    -- See Note [Dependencies for datatype bindings, and pruning them]
    vDeps <- tyVarDeclDeps d
    tvDeps <- traverse tyVarDeclDeps tvs
    cstrDeps <- traverse varDeclDeps constrs
    -- Destructors depend on the datatype and the argument types of all the constructors,
    -- because e.g. a destructor for Maybe looks like:
    -- forall a . Maybe a -> (a -> r) -> r -> r
    -- i.e. the argument type of the Just constructor appears as the argument to the branch.
    --
    -- We can get the effect of that by having it depend on all the constructor types
    -- (which also include the datatype).
    -- This is more diligent than currently necessary since we're going to make all the
    -- term-level parts depend on each other later, but it's good practice and will be
    -- useful if we ever stop doing that.
    destrDeps <-
      G.overlays
        <$> (withCurrent destr $ traverse (typeDeps . _varDeclType) constrs)
    let tus = fmap (view PLC.theUnique) (destr : fmap _varDeclName constrs)
    -- See Note [Dependencies for datatype bindings, and pruning them]
    let nonDatatypeClique = G.clique (fmap Variable tus)
    pure $ G.overlays $ [vDeps] ++ tvDeps ++ cstrDeps ++ [destrDeps] ++ [nonDatatypeClique]

varDeclDeps ::
  ( DepGraph g
  , MonadReader (DepCtx tyname name uni fun) m
  , PLC.HasUnique tyname PLC.TypeUnique
  , PLC.HasUnique name PLC.TermUnique
  ) =>
  VarDecl tyname name uni a ->
  m g
varDeclDeps (VarDecl _ n ty) = withCurrent n $ typeDeps ty

-- Here for completeness, but doesn't do much
tyVarDeclDeps ::
  (G.Graph g, MonadReader (DepCtx tyname name uni fun) m) =>
  TyVarDecl tyname a ->
  m g
tyVarDeclDeps _ = pure G.empty

{- | Compute the dependency graph of a term. Takes an initial 'Node' indicating what the
term itself depends on (usually 'Root' if it is the real term you are interested in).
-}
termDeps ::
  ( DepGraph g
  , MonadReader (DepCtx tyname name uni fun) m
  , PLC.HasUnique tyname PLC.TypeUnique
  , PLC.HasUnique name PLC.TermUnique
  , PLC.ToBuiltinMeaning uni fun
  ) =>
  Term tyname name uni fun a ->
  m g
termDeps = \case
  Let _ _ bs t -> do
    bGraphs <- traverse bindingDeps bs
    bodyGraph <- termDeps t
    pure . G.overlays . NE.toList $ bodyGraph NE.<| bGraphs
  Var _ n -> currentDependsOn [n ^. PLC.theUnique]
  x -> do
    tds <- traverse termDeps (x ^.. termSubterms)
    tyds <- traverse typeDeps (x ^.. termSubtypes)
    pure $ G.overlays $ tds ++ tyds

{- | Compute the dependency graph of a type. Takes an initial 'Node' indicating what
the type itself depends on (usually 'Root' if it is the real type you are interested in).
-}
typeDeps ::
  (DepGraph g, MonadReader (DepCtx tyname name uni fun) m, PLC.HasUnique tyname PLC.TypeUnique) =>
  Type tyname uni a ->
  m g
typeDeps ty =
  -- The dependency graph of a type is very simple since it doesn't have any internal
  -- let-bindings. So we just need to find all the used variables and mark them as
  -- dependencies of the current node.
  let used = Usages.allUsed $ Usages.typeUsages ty
   in currentDependsOn (Set.toList used)
