{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

{-| Mutual recursion inlining.

Given a @let rec@ group, this pass identifies helper bindings — those not
used by the body (non-roots), not self-recursive, called from exactly one
sibling, and used exactly once there — and inlines them into their caller.
This works across independent subgroups within the same @let rec@, e.g.
@{even, odd, f, g}@ where @{even, odd}@ and @{f, g}@ are separate cycles.

No beta reduction is performed here; the resulting unsaturated applications
are left for downstream passes to clean up. -}
module PlutusIR.Transform.RecInline
  ( recInline
  , recInlinePass
  , recInlinePassSC
  ) where

import Algebra.Graph.AdjacencyMap qualified as Graph
import Control.Lens (traverseOf, (^.))
import Control.Monad (guard)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
import Data.Set qualified as Set
import PlutusCore qualified as PLC
import PlutusCore.Arity (Arity, Param (TermParam, TypeParam))
import PlutusCore.Name.Unique qualified as Unique
import PlutusCore.Quote (MonadQuote)
import PlutusIR
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.Contexts (Saturation (Saturated), fillAppContext, saturates, splitApplication)
import PlutusIR.Pass
import PlutusIR.Transform.Rename ()
import PlutusIR.TypeCheck qualified as TC

{-| A single term binding within a recursive group, carrying cached usage and
arity information so we don't recompute them on every step. -}
data RecBinding uni fun a = RecBinding
  { rbAnn :: a
  , rbStrictness :: Strictness
  , rbDecl :: VarDecl TyName Name uni a
  , rbRhs :: Term TyName Name uni fun a
  , rbUsages :: Usages.Usages
  , rbArity :: Arity
  }

rbName :: RecBinding uni fun a -> Name
rbName RecBinding {rbDecl = VarDecl _ n _} = n

{-| A recursive binding group together with its call graph.
"Roots" are the bindings actually referenced by the @let@ body. -}
data RecGroup uni fun a = RecGroup
  { rgBindings :: Map.Map Unique.Unique (RecBinding uni fun a)
  , rgOrder :: [Unique.Unique]
  , rgRoots :: Set.Set Unique.Unique
  , rgGraph :: Graph.AdjacencyMap Unique.Unique
  }

-- | Count leading lambda/type abstractions to determine a term's arity.
rhsArity :: Term tyname name uni fun a -> Arity
rhsArity = go []
  where
    go acc = \case
      LamAbs _ _ _ t -> go (TermParam : acc) t
      TyAbs _ _ _ t -> go (TypeParam : acc) t
      _ -> reverse acc

recInlinePassSC
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, MonadQuote m, Ord a)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
recInlinePassSC tcconfig = renamePass <> recInlinePass tcconfig

recInlinePass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, MonadQuote m, Ord a)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
recInlinePass tcconfig =
  NamedPass "recursive inlining" $
    Pass
      recInline
      [Typechecks tcconfig, GloballyUniqueNames]
      [ConstCondition (Typechecks tcconfig), ConstCondition GloballyUniqueNames]

-- | Walk the term bottom-up, attempting to collapse each @let rec@ group.
recInline
  :: MonadQuote m
  => Term TyName Name uni fun a
  -> m (Term TyName Name uni fun a)
recInline = go
  where
    go term = do
      term' <- traverseOf termSubterms go term
      case term' of
        Let ann Rec bs body -> rewriteRecGroup ann bs body
        _ -> pure term'

{-| Try to collapse a recursive group by inlining helpers. If we manage to
eliminate at least one binding, emit the smaller group; otherwise return the
original term unchanged. -}
rewriteRecGroup
  :: MonadQuote m
  => a
  -> NE.NonEmpty (Binding TyName Name uni fun a)
  -> Term TyName Name uni fun a
  -> m (Term TyName Name uni fun a)
rewriteRecGroup ann bs body =
  case mkRecGroup bs body of
    Nothing -> pure original
    Just group -> do
      collapsed <- collapseRecGroup group
      pure $ fromMaybe original (extractResult group collapsed)
  where
    original = Let ann Rec bs body
    extractResult orig col = do
      guard (length (rgOrder col) < length (rgOrder orig))
      bs' <-
        NE.nonEmpty
          [ TermBind (rbAnn b) (rbStrictness b) (rbDecl b) (rbRhs b)
          | key <- rgOrder col
          , Just b <- [Map.lookup key (rgBindings col)]
          ]
      pure $ Let ann Rec bs' body

{-| Build a 'RecGroup' from the raw bindings, or 'Nothing' if the group is
not eligible (non-term bindings, fewer than 2 members, or non-function
bindings). -}
mkRecGroup
  :: NE.NonEmpty (Binding TyName Name uni fun a)
  -> Term TyName Name uni fun a
  -> Maybe (RecGroup uni fun a)
mkRecGroup bs body = do
  bindings <- traverse asRecBinding (NE.toList bs)
  guard (length bindings > 1)
  guard (all (not . null . rbArity) bindings)
  let key b = rbName b ^. Unique.theUnique
      bindingMap = Map.fromList [(key b, b) | b <- bindings]
      roots = Map.keysSet bindingMap `Set.intersection` Usages.allUsed (Usages.termUsages body)
  pure $ buildGraph (fmap key bindings) bindingMap roots
  where
    asRecBinding = \case
      TermBind bindAnn strictness decl rhs ->
        Just
          RecBinding
            { rbAnn = bindAnn
            , rbStrictness = strictness
            , rbDecl = decl
            , rbRhs = rhs
            , rbUsages = Usages.termUsages rhs
            , rbArity = rhsArity rhs
            }
      _ -> Nothing

{-| Construct a 'RecGroup' by computing the intra-group call graph from the
cached usage information on each binding. -}
buildGraph
  :: [Unique.Unique]
  -> Map.Map Unique.Unique (RecBinding uni fun a)
  -> Set.Set Unique.Unique
  -> RecGroup uni fun a
buildGraph order bindings roots =
  RecGroup {rgBindings = bindings, rgOrder = order, rgRoots = roots, rgGraph = graph}
  where
    graph =
      Graph.fromAdjacencySets
        [ (key, keys `Set.intersection` Usages.allUsed (rbUsages b))
        | (key, b) <- Map.toList bindings
        ]
    keys = Map.keysSet bindings

{-| Iteratively inline helpers into their callers until no more candidates
remain. -}
collapseRecGroup
  :: MonadQuote m
  => RecGroup uni fun a
  -> m (RecGroup uni fun a)
collapseRecGroup group =
  case findCandidate group of
    Nothing -> pure group
    Just (hostKey, helperKey) ->
      tryInline group hostKey helperKey >>= \case
        Just group' -> collapseRecGroup group'
        Nothing -> pure group

{-| Find a helper eligible for inlining: not a root, not self-recursive,
called from exactly one sibling, and used exactly once in that sibling. -}
findCandidate :: RecGroup uni fun a -> Maybe (Unique.Unique, Unique.Unique)
findCandidate group = listToMaybe $ mapMaybe check (rgOrder group)
  where
    check helper = do
      guard (helper `Set.notMember` rgRoots group)
      guard (helper `Set.notMember` Graph.postSet helper (rgGraph group))
      host <- case Set.toList (Set.delete helper $ Graph.preSet helper (rgGraph group)) of
        [h] -> Just h
        _ -> Nothing
      helperBinding <- Map.lookup helper (rgBindings group)
      hostBinding <- Map.lookup host (rgBindings group)
      guard (Usages.getUsageCount (rbName helperBinding) (rbUsages hostBinding) == 1)
      pure (host, helper)

{-| Inline all saturated calls to the helper within the host's RHS.
If successful (all references eliminated), remove the helper from the group. -}
tryInline
  :: MonadQuote m
  => RecGroup uni fun a
  -> Unique.Unique
  -> Unique.Unique
  -> m (Maybe (RecGroup uni fun a))
tryInline group hostKey helperKey =
  case (Map.lookup hostKey (rgBindings group), Map.lookup helperKey (rgBindings group)) of
    (Just host, Just helper) -> do
      hostRhs' <- inlineCallsOf (rbName helper) (rbRhs helper) (rbRhs host)
      pure $ do
        guard (Usages.getUsageCount (rbName helper) (Usages.termUsages hostRhs') == 0)
        let updated = host {rbRhs = hostRhs', rbUsages = Usages.termUsages hostRhs', rbArity = rhsArity hostRhs'}
            bindings = Map.delete helperKey $ Map.insert hostKey updated (rgBindings group)
            order = filter (/= helperKey) (rgOrder group)
        pure $ buildGraph order bindings (rgRoots group)
    _ -> pure Nothing

{-| Replace saturated calls to a helper with the helper's RHS applied to the
same arguments. Each substitution uses a fresh rename to avoid capture. -}
inlineCallsOf
  :: MonadQuote m
  => Name
  -> Term TyName Name uni fun a
  -> Term TyName Name uni fun a
  -> m (Term TyName Name uni fun a)
inlineCallsOf helperName helperRhs = go
  where
    go term = do
      term' <- traverseOf termSubterms go term
      case splitApplication term' of
        (Var _ name, args) | name == helperName -> do
          rhs' <- PLC.rename helperRhs
          pure $ case saturates args (rhsArity rhs') of
            Just Saturated -> fillAppContext rhs' args
            _ -> term'
        _ -> pure term'
