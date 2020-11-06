{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeOperators    #-}
-- | Functions for computing the dependency graph of variables within a term or type. A "dependency" between
-- two nodes "A depends on B" means that B cannot be removed from the program without also removing A.
module Language.PlutusIR.Analysis.Dependencies (Node (..), DepGraph, StrictnessMap, runTermDeps, runTypeDeps) where

import qualified Language.PlutusCore               as PLC
import qualified Language.PlutusCore.Constant      as PLC
import qualified Language.PlutusCore.Name          as PLC

import           Language.PlutusIR
import qualified Language.PlutusIR.Analysis.Usages as Usages
import           Language.PlutusIR.Purity

import           Control.Lens                      hiding (Strict)
import           Control.Monad.Reader
import           Control.Monad.State

import qualified Algebra.Graph.Class               as G
import qualified Data.Map                          as Map
import qualified Data.Set                          as Set

import qualified Data.List.NonEmpty                as NE

import           Data.Foldable

type DepCtx term = Node
type StrictnessMap = Map.Map PLC.Unique Strictness
type DepState = StrictnessMap

-- | A node in a dependency graph. Either a specific 'PLC.Unique', or a specific
-- node indicating the root of the graph. We need the root node because when computing the
-- dependency graph of, say, a term, there will not be a binding for the term itself which
-- we can use to represent it in the graph.
data Node = Variable PLC.Unique | Root deriving (Show, Eq, Ord)

-- | A constraint requiring @g@ to be a 'G.Graph' (so we can compute e.g. a @Relation@ from it), whose
-- vertices are 'Node's.
type DepGraph g = (G.Graph g, (G.Vertex g)~Node)

varStrictnessFun ::
    (MonadState DepState m, PLC.HasUnique name u)
    => m (name -> Strictness)
varStrictnessFun = do
    strictnessMap <- get
    pure $ \n' -> Map.findWithDefault NonStrict (n' ^. PLC.theUnique) strictnessMap

-- | Compute the dependency graph of a 'Term'. The 'Root' node will correspond to the term itself.
--
-- For example, the graph of @[(let (nonrec) (vardecl x t) y) [x z]]@ is
-- @
--     ROOT -> x
--     ROOT -> z
--     x -> y
--     x -> t
-- @
runTermDeps
    :: (DepGraph g, PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique,
       PLC.ToBuiltinMeaning uni fun)
    => Term tyname name uni fun a
    -> (g, StrictnessMap)
runTermDeps t = flip runState mempty $ flip runReaderT Root $ termDeps t

-- | Compute the dependency graph of a 'Type'. The 'Root' node will correspond to the type itself.
--
-- This graph will always be simply a star from 'Root', since types have no internal let-bindings.
--
-- For example, the graph of @(all a (type) [f a])@ is:
-- @
--     ROOT -> f
--     ROOT -> a
-- @
--
runTypeDeps
    :: (DepGraph g, PLC.HasUnique tyname PLC.TypeUnique)
    => Type tyname uni a
    -> g
runTypeDeps t = flip runReader Root $ typeDeps t

-- | Record some dependencies on the current node.
currentDependsOn
    :: (DepGraph g, MonadReader (DepCtx term) m)
    => [PLC.Unique]
    -> m g
currentDependsOn us = do
    current <- ask
    pure $ G.connect (G.vertices [current]) (G.vertices (fmap Variable us))

-- | Process the given action with the given name as the current node.
withCurrent
    :: (MonadReader (DepCtx term) m, PLC.HasUnique n u)
    => n
    -> m g
    -> m g
withCurrent n = local $ \_ -> Variable $ n ^. PLC.theUnique

{- Note [Strict term bindings and dependencies]
A node inside a strict let binding can incur a dependency on it even if the defined variable is unused.

Consider:

let strict x = error in y

This evaluates to error, because the RHS of a strict binding is evaluated when we evaluate the let-term.

We only care about this for its *effects*: the variable itself is still unused. So we only need to
worry in the case where the RHS is not a value. If it *is* a value, then evaluating it is a noop, so there
can be no effects that we're missing. Essentially we are using "is a value" as an under-approximation of
"is pure".

From the point of view of our algorithm, we handle the dependency by treating it as though there was an
reference to the newly bound variable alongside the binding, but only in the cases where it matters.
-}

bindingDeps
    :: (DepGraph g, MonadReader (DepCtx term) m, MonadState DepState m, PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique,
       PLC.ToBuiltinMeaning uni fun)
    => Binding tyname name uni fun a
    -> m g
bindingDeps b = case b of
    TermBind _ strictness d@(VarDecl _ n _) rhs -> do
        vDeps <- varDeclDeps d
        tDeps <- withCurrent n $ termDeps rhs

        -- See Note [Strict term bindings and dependencies]
        strictnessFun <- varStrictnessFun
        evalDeps <- case strictness of
            Strict | not (isPure strictnessFun rhs) -> currentDependsOn [n ^. PLC.theUnique]
            _                                       -> pure G.empty

        pure $ G.overlays [vDeps, tDeps, evalDeps]
    TypeBind _ d@(TyVarDecl _ n _) rhs -> do
        vDeps <- tyVarDeclDeps d
        tDeps <- withCurrent n $ typeDeps rhs
        pure $ G.overlay vDeps tDeps
    DatatypeBind _ (Datatype _ d tvs destr constrs) -> do
        vDeps <- tyVarDeclDeps d
        tvDeps <- traverse tyVarDeclDeps tvs
        cstrDeps <- traverse varDeclDeps constrs
        -- All the datatype bindings depend on each other since they can't be used separately. Consider
        -- the identity function on a datatype type - it only uses the type variable, but the whole definition
        -- will therefore be kept, and so we must consider any uses in e.g. the constructors as live.
        let tyus = fmap (view PLC.theUnique) $ tyVarDeclName d : fmap tyVarDeclName tvs
        let tus = fmap (view PLC.theUnique) $ destr : fmap varDeclName constrs
        let localDeps = G.clique (fmap Variable $ tyus ++ tus)
        pure $ G.overlays $ [vDeps] ++ tvDeps ++ cstrDeps ++ [localDeps]

bindingStrictness
    :: (MonadState DepState m, PLC.HasUnique name PLC.TermUnique)
    => Binding tyname name uni fun a
    -> m ()
bindingStrictness b = case b of
    TermBind _ strictness (VarDecl _ n _) _ -> modify (Map.insert (n ^. PLC.theUnique) strictness)
    TypeBind {} -> pure ()
    DatatypeBind _ (Datatype _ _ _ destr constrs) -> do
        -- Constructors and destructor are bound strictly
        for_ constrs $ \(VarDecl _ n _) -> modify (Map.insert (n ^. PLC.theUnique) Strict)
        modify (Map.insert (destr ^. PLC.theUnique) Strict)

varDeclDeps
    :: (DepGraph g, MonadReader (DepCtx term) m, PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
    => VarDecl tyname name uni fun a
    -> m g
varDeclDeps (VarDecl _ n ty) = withCurrent n $ typeDeps ty

-- Here for completeness, but doesn't do much
tyVarDeclDeps
    :: (G.Graph g, MonadReader (DepCtx term) m)
    => TyVarDecl tyname a
    -> m g
tyVarDeclDeps _ = pure G.empty

-- | Compute the dependency graph of a term. Takes an initial 'Node' indicating what the term itself depends on
-- (usually 'Root' if it is the real term you are interested in).
termDeps
    :: (DepGraph g, MonadReader (DepCtx term) m, MonadState DepState m, PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique,
       PLC.ToBuiltinMeaning uni fun)
    => Term tyname name uni fun a
    -> m g
termDeps = \case
    Let _ _ bs t -> do
        -- Need to do this before processing the RHSs of the bindings, as recursive bindings may need to know about
        -- the strictnesses of other variables.
        traverse_ bindingStrictness bs
        bGraphs <- traverse bindingDeps bs
        bodyGraph <- termDeps t
        pure . G.overlays . NE.toList $ bodyGraph NE.<| bGraphs
    Var _ n -> currentDependsOn [n ^. PLC.theUnique]
    LamAbs _ n ty t -> do
        -- Record that lambda-bound variables are strict
        modify (Map.insert (n ^. PLC.theUnique) Strict)
        tds <- termDeps t
        tyds <- typeDeps ty
        pure $ G.overlays $ [tds, tyds]
    x -> do
        tds <- traverse termDeps (x ^.. termSubterms)
        tyds <- traverse typeDeps (x ^.. termSubtypes)
        pure $ G.overlays $ tds ++ tyds

-- | Compute the dependency graph of a type. Takes an initial 'Node' indicating what the type itself depends on
-- (usually 'Root' if it is the real type you are interested in).
typeDeps
    :: (DepGraph g, MonadReader (DepCtx term) m, PLC.HasUnique tyname PLC.TypeUnique)
    => Type tyname uni a
    -> m g
typeDeps ty =
    -- The dependency graph of a type is very simple since it doesn't have any internal let-bindings. So we just
    -- need to find all the used variables and mark them as dependencies of the current node.
    let used = Usages.allUsed $ Usages.runTypeUsages ty
    in currentDependsOn (Set.toList used)
