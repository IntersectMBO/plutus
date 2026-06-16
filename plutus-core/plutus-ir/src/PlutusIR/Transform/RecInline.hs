{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

{-| Mutual recursion inlining.

Given a @let rec@ group, this pass identifies helper bindings — those not
used by the body (non-roots), not self-recursive, and safe to inline according
to the same size/cost heuristics as the main inliner — and inlines them into
their callers.
This works across independent subgroups within the same @let rec@, e.g.
@{even, odd, f, g}@ where @{even, odd}@ and @{f, g}@ are separate cycles.

No beta reduction is performed here; the resulting applications
are left for downstream passes to clean up. -}
module PlutusIR.Transform.RecInline
  ( recInline
  , recInlinePass
  , recInlinePassSC
  ) where

import Algebra.Graph.AdjacencyMap qualified as Graph
import Control.Lens (transformMOf, (^.))
import Control.Monad (guard)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set qualified as Set
import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name.Unique qualified as Unique
import PlutusCore.Quote (MonadQuote)
import PlutusIR
import PlutusIR.Analysis.Builtins (BuiltinsInfo)
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.Analysis.VarInfo (termVarInfo)
import PlutusIR.Pass
import PlutusIR.Purity (isPure)
import PlutusIR.Transform.Inline.Utils (costIsAcceptable, sizeIsAcceptable)
import PlutusIR.Transform.Rename ()
import PlutusIR.TypeCheck qualified as TC

{-| A single term binding within a recursive group, carrying cached usage
information so we don't recompute it on every step. -}
data RecBinding uni fun a = RecBinding
  { rbAnn :: a
  , rbStrictness :: Strictness
  , rbDecl :: VarDecl TyName Name uni a
  , rbRhs :: Term TyName Name uni fun a
  , rbUsages :: Usages.Usages
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

data InlineCandidate = InlineCandidate Unique.Unique Bool

recInlinePassSC
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, MonadQuote m, Ord a)
  => BuiltinsInfo uni fun
  -> Bool
  -> TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
recInlinePassSC binfo inlineConstants tcconfig =
  renamePass <> recInlinePass binfo inlineConstants tcconfig

recInlinePass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, MonadQuote m, Ord a)
  => BuiltinsInfo uni fun
  -> Bool
  -> TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
recInlinePass binfo inlineConstants tcconfig =
  NamedPass "recursive inlining" $
    Pass
      (recInline binfo inlineConstants)
      [Typechecks tcconfig, GloballyUniqueNames]
      [ConstCondition (Typechecks tcconfig), ConstCondition GloballyUniqueNames]

-- | Walk the term bottom-up, attempting to collapse each @let rec@ group.
recInline
  :: (PLC.ToBuiltinMeaning uni fun, MonadQuote m)
  => BuiltinsInfo uni fun
  -> Bool
  -> Term TyName Name uni fun a
  -> m (Term TyName Name uni fun a)
recInline binfo inlineConstants =
  transformMOf termSubterms $ \case
    Let ann Rec bs body -> rewriteRecGroup binfo inlineConstants ann bs body
    term -> pure term

{-| Try to collapse a recursive group by inlining helpers. If we manage to
eliminate at least one binding, emit the smaller group; otherwise return the
original term unchanged. -}
rewriteRecGroup
  :: (PLC.ToBuiltinMeaning uni fun, MonadQuote m)
  => BuiltinsInfo uni fun
  -> Bool
  -> a
  -> NE.NonEmpty (Binding TyName Name uni fun a)
  -> Term TyName Name uni fun a
  -> m (Term TyName Name uni fun a)
rewriteRecGroup binfo inlineConstants ann bs body =
  case mkRecGroup binfo ann bs body of
    Nothing -> pure original
    Just (group, passthrough) -> do
      collapsed <- collapseRecGroup inlineConstants group
      pure $ fromMaybe original (extractResult group collapsed passthrough)
  where
    original = Let ann Rec bs body
    extractResult orig col passthrough = do
      -- At least one helper was inlined away.
      guard (length (rgOrder col) < length (rgOrder orig))
      let collapsed =
            [ TermBind (rbAnn b) (rbStrictness b) (rbDecl b) (rbRhs b)
            | key <- rgOrder col
            , Just b <- [Map.lookup key (rgBindings col)]
            ]
      bs' <- NE.nonEmpty (collapsed ++ passthrough)
      pure $ Let ann Rec bs' body

{-| Extract eligible function bindings from a @let rec@ group. Returns
the 'RecGroup' and any passthrough bindings (type bindings, datatype bindings,
effectful strict value bindings) that are left untouched. Returns 'Nothing' if
fewer than 2 safe term bindings are found. -}
mkRecGroup
  :: PLC.ToBuiltinMeaning uni fun
  => BuiltinsInfo uni fun
  -> a
  -> NE.NonEmpty (Binding TyName Name uni fun a)
  -> Term TyName Name uni fun a
  -> Maybe (RecGroup uni fun a, [Binding TyName Name uni fun a])
mkRecGroup binfo ann bs body = do
  let paired = [(b, asRecBinding b) | b <- NE.toList bs]
      -- Safe term bindings that we can try to collapse.
      eligible = [rb | (_, Just rb) <- paired]
      -- Everything else: type bindings, datatype bindings, and effectful
      -- strict value bindings.
      passthrough = [b | (b, Nothing) <- paired]
  -- Need at least 2 bindings to have anything to collapse.
  guard (length eligible > 1)
  let key b = rbName b ^. Unique.theUnique
      bindingMap = Map.fromList [(key b, b) | b <- eligible]
      -- Bindings used by the let body or by passthrough bindings are roots —
      -- inlining them away would break references from outside the group.
      bodyUsed = Usages.allUsed (Usages.termUsages body)
      passthroughUsed =
        Set.unions
          [ Usages.allUsed (Usages.termUsages rhs)
          | TermBind _ _ _ rhs <- passthrough
          ]
      roots =
        Map.keysSet bindingMap
          `Set.intersection` (bodyUsed `Set.union` passthroughUsed)
  pure (buildGraph (fmap key eligible) bindingMap roots, passthrough)
  where
    vinfo = termVarInfo (Let ann Rec bs body)

    asRecBinding = \case
      TermBind bindAnn strictness decl rhs
        | let rhsPure = isPure binfo vinfo rhs
        , strictness == NonStrict || rhsPure ->
            Just
              RecBinding
                { rbAnn = bindAnn
                , rbStrictness = strictness
                , rbDecl = decl
                , rbRhs = rhs
                , rbUsages = Usages.termUsages rhs
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
  => Bool
  -> RecGroup uni fun a
  -> m (RecGroup uni fun a)
collapseRecGroup inlineConstants group = tryCandidates (findCandidates inlineConstants group)
  where
    tryCandidates [] = pure group
    tryCandidates (candidate : rest) =
      tryInline group candidate >>= \case
        Just group' -> collapseRecGroup inlineConstants group'
        Nothing -> tryCandidates rest

{-| Find helpers eligible for inlining: not roots, not self-recursive, and
acceptable according to the main inliner's single-use/size/cost criteria. -}
findCandidates :: Bool -> RecGroup uni fun a -> [InlineCandidate]
findCandidates inlineConstants group = mapMaybe check (rgOrder group)
  where
    check helper = do
      -- Roots are used by the let body — removing them would change semantics.
      guard (helper `Set.notMember` rgRoots group)
      -- Self-recursive helpers can't be fully eliminated by inlining.
      guard (helper `Set.notMember` Graph.postSet helper (rgGraph group))
      helperBinding <- Map.lookup helper (rgBindings group)
      let totalUses =
            sum
              [ Usages.getUsageCount (rbName helperBinding) (rbUsages binding)
              | (key, binding) <- Map.toList (rgBindings group)
              , key /= helper
              ]
      guard (totalUses > 0)
      guard $
        totalUses == 1
          || ( costIsAcceptable (rbRhs helperBinding)
                 && sizeIsAcceptable inlineConstants (rbRhs helperBinding)
             )
      pure $ InlineCandidate helper (totalUses > 1)

{-| Inline all references to the helper within the rest of the recursive group.
If successful, remove the helper from the group. -}
tryInline
  :: MonadQuote m
  => RecGroup uni fun a
  -> InlineCandidate
  -> m (Maybe (RecGroup uni fun a))
tryInline group (InlineCandidate helperKey needsRename) =
  case Map.lookup helperKey (rgBindings group) of
    Just helper -> do
      let helperName = rbName helper
      updatedBindings <-
        traverse
          (updateBinding helperName (rbRhs helper))
          (Map.toList $ Map.delete helperKey (rgBindings group))
      let bindings = Map.fromList updatedBindings
      pure $ do
        -- Verify all references were eliminated before removing the binding.
        guard $
          all
            ( \binding ->
                Usages.getUsageCount helperName (rbUsages binding) == 0
            )
            (Map.elems bindings)
        let order = filter (/= helperKey) (rgOrder group)
        pure $ buildGraph order bindings (rgRoots group)
    _ -> pure Nothing
  where
    updateBinding helperName helperRhs (key, binding) = do
      rhs' <- inlineCallsOf needsRename helperName helperRhs (rbRhs binding)
      let updated =
            binding
              { rbRhs = rhs'
              , rbUsages = Usages.termUsages rhs'
              }
      pure (key, updated)

{-| Replace helper variables with the helper's RHS. Multi-use substitutions use
a fresh rename for each occurrence; single-use substitutions move the original
RHS so they do not perturb fresh-name allocation unnecessarily. -}
inlineCallsOf
  :: MonadQuote m
  => Bool
  -> Name
  -> Term TyName Name uni fun a
  -> Term TyName Name uni fun a
  -> m (Term TyName Name uni fun a)
inlineCallsOf needsRename helperName helperRhs =
  transformMOf termSubterms $ \case
    Var _ name
      | name == helperName ->
          if needsRename
            then PLC.rename helperRhs
            else pure helperRhs
    term -> pure term
