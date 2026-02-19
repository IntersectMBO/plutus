{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-| An inlining pass.

This pass is essentially a copy of the PIR inliner, and should be KEPT IN SYNC
with it. It's hard to do this with true abstraction, so we just have to keep
two copies reasonably similar.

However, there are some differences. In the interests of making it easier
to keep things in sync, these are explicitly listed in
Note [Differences from PIR inliner]. If you add another difference,
please note it there! Obviously fewer differences is better.

See Note [The problem of inlining destructors] for why this pass exists. -}
module UntypedPlutusCore.Transform.Inline
  ( inline
  , InlineHints (..)

    -- * Exported for testing
  , InlineM
  , S (..)
  , Decoration (..)
  , Ann
  , InlineInfo (..)
  , Subst (..)
  , TermEnv (..)
  , isFirstVarBeforeEffects
  , isStrictIn
  , effectSafe
  ) where

import Control.Lens (Lens', forMOf, makeLenses, view, (%~), (&), (^.), _1)
import Control.Monad.Extra (ifM, (&&^), (||^))
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State (StateT, evalStateT, gets, modify')
import Data.Bifunctor (first)
import Data.Vector qualified as V
import PlutusCore qualified as PLC
import PlutusCore.Annotation (Inline (AlwaysInline, SafeToInline), InlineHints (..))
import PlutusCore.Builtin (ToBuiltinMeaning (BuiltinSemanticsVariant))
import PlutusCore.Builtin qualified as PLC
import PlutusCore.MkPlc (mkIterApp)
import PlutusCore.Name.Unique (HasUnique, TermUnique (..), Unique (..))
import PlutusCore.Name.UniqueMap qualified as UMap
import PlutusCore.Quote (MonadQuote (..), Quote)
import PlutusCore.Rename (Dupable, dupable, liftDupable)
import PlutusPrelude (Generic)
import UntypedPlutusCore.Analysis.Usages qualified as Usages
import UntypedPlutusCore.AstSize (AstSize, termAstSize)
import UntypedPlutusCore.Core qualified as UPLC
import UntypedPlutusCore.Core.Plated (termSubterms)
import UntypedPlutusCore.Core.Type (Term (..), modifyTermAnn, termAnn)
import UntypedPlutusCore.MkUPlc (Def (..), UTermDef, UVarDecl (..))
import UntypedPlutusCore.Purity
  ( EvalTerm (EvalTerm, Unknown)
  , Purity (MaybeImpure, Pure)
  , isPure
  , termEvaluationOrder
  , unEvalOrder
  )
import UntypedPlutusCore.Rename ()
import UntypedPlutusCore.Subst (termSubstNamesM)
import UntypedPlutusCore.Transform.Certify.Hints qualified as CertifierHints
import UntypedPlutusCore.Transform.Simplifier
  ( SimplifierStage (Inline)
  , SimplifierT
  , recordSimplificationWithHints
  )

{- Note [Differences from PIR inliner]
See the module comment for explanation for why this exists and is similar to
the PIR inliner.

1. No types (obviously).
2. No strictness information (we only have lambda arguments, which are always
   strict).
3. Handling of multiple beta-reductions in one go, this is handled in PIR by a
   dedicated pass.
4. Simplistic purity analysis, in particular we don't try to be clever about
   builtins (should mostly be handled in PIR).
-}

-- | Substitution range, 'SubstRng' in the paper.
newtype InlineTerm name uni fun a = Done (Dupable (Term name uni fun a))

{-| Term substitution, 'Subst' in the paper.
A map of unprocessed variable and its substitution range. -}
newtype TermEnv name uni fun a = TermEnv
  {_unTermEnv :: PLC.UniqueMap TermUnique (InlineTerm name uni fun a)}
  deriving newtype (Semigroup, Monoid)

{-| Wrapper of term substitution so that it's similar to the PIR inliner.
See Note [Differences from PIR inliner] 1 -}
newtype Subst name uni fun a = Subst {_termEnv :: TermEnv name uni fun a}
  deriving stock (Generic)
  deriving newtype (Semigroup, Monoid)

makeLenses ''TermEnv
makeLenses ''Subst

data VarInfo name uni fun ann = VarInfo
  { _varBinders :: [(name, ann)]
  -- ^ Lambda binders in the RHS (definition) of the variable.
  , _varRhs :: Term name uni fun ann
  -- ^ The RHS (definition) of the variable.
  , _varRhsBody :: InlineTerm name uni fun ann
  {-^ The body of the RHS of the variable (i.e., RHS minus the binders).
  Using 'InlineTerm' here to ensure the body is renamed when inlined. -}
  }

makeLenses ''VarInfo

-- | UPLC inliner state
data S name uni fun a = S
  { _subst :: Subst name uni fun a
  , _vars :: PLC.UniqueMap TermUnique (VarInfo name uni fun a)
  }

makeLenses ''S

instance Semigroup (S name uni fun a) where
  S a1 b1 <> S a2 b2 = S (a1 <> a2) (b1 <> b2)

instance Monoid (S name uni fun a) where
  mempty = S mempty mempty

type ExternalConstraints name uni fun m =
  ( HasUnique name TermUnique
  , Eq name
  , PLC.ToBuiltinMeaning uni fun
  , MonadQuote m
  )

type InliningConstraints name uni fun =
  ( HasUnique name TermUnique
  , Eq name
  , PLC.ToBuiltinMeaning uni fun
  )

-- See Note [Differences from PIR inliner] 2
data InlineInfo name fun a = InlineInfo
  { _iiUsages :: Usages.Usages
  , _iiHints :: InlineHints name a
  , _iiBuiltinSemanticsVariant :: PLC.BuiltinSemanticsVariant fun
  , _iiInlineConstants :: Bool
  , _iiInlineCallsiteGrowth :: AstSize
  , _iiPreserveLogging :: Bool
  }

makeLenses ''InlineInfo

-- Using a concrete monad makes a very large difference to the performance
-- of this module (determined from profiling)

-- | The monad the inliner runs in.
type InlineM name uni fun a =
  ReaderT (InlineInfo name fun a) (StateT (S name uni fun (Ann a)) Quote)

-- | Look up the unprocessed variable in the substitution.
lookupTerm
  :: HasUnique name TermUnique
  => name
  -> S name uni fun a
  -> Maybe (InlineTerm name uni fun a)
lookupTerm n s = UMap.lookupName n $ s ^. subst . termEnv . unTermEnv

-- | Insert the unprocessed variable into the substitution.
extendTerm
  :: HasUnique name TermUnique
  => name
  -- ^ The name of the variable.
  -> InlineTerm name uni fun a
  -- ^ The substitution range.
  -> S name uni fun a
  -- ^ The substitution.
  -> S name uni fun a
extendTerm n clos s =
  s & subst . termEnv . unTermEnv %~ UMap.insertByName n clos

lookupVarInfo
  :: HasUnique name TermUnique
  => name
  -> S name uni fun a
  -> Maybe (VarInfo name uni fun a)
lookupVarInfo n s = UMap.lookupName n $ s ^. vars

extendVarInfo
  :: HasUnique name TermUnique
  => name
  -> VarInfo name uni fun a
  -> S name uni fun a
  -> S name uni fun a
extendVarInfo n info s = s & vars %~ UMap.insertByName n info

{-| Inline simple bindings. Relies on global uniqueness, and preserves it.
See Note [Inlining and global uniqueness] -}
inline
  :: forall name uni fun m a
   . ExternalConstraints name uni fun m
  => AstSize
  -- ^ inline threshold
  -> Bool
  -- ^ inline constants
  -> Bool
  -- ^ preserve logging
  -> InlineHints name a
  -> PLC.BuiltinSemanticsVariant fun
  -> Term name uni fun a
  -> SimplifierT name uni fun a m (Term name uni fun a)
inline
  callsiteGrowth
  inlineConstants
  preserveLogging
  hints
  builtinSemanticsVariant
  t = do
    decoratedResult <-
      liftQuote $
        flip evalStateT mempty $
          runReaderT
            (processTerm (emptyDecoration <$> t))
            InlineInfo
              { _iiUsages = Usages.termUsages t
              , _iiHints = hints
              , _iiBuiltinSemanticsVariant = builtinSemanticsVariant
              , _iiInlineConstants = inlineConstants
              , _iiInlineCallsiteGrowth = callsiteGrowth
              , _iiPreserveLogging = preserveLogging
              }
    let result = snd <$> decoratedResult
    recordSimplificationWithHints (CertifierHints.Inline (mkHints decoratedResult)) t Inline result
    return result

-- See Note [Differences from PIR inliner] 3

{-| Extract the list of applications from a term,
a bit like a "multi-beta" reduction.

Some examples will help (annotations are omitted):
[(\x . t) a] -> Just ([(x, a)], t)

[[[(\x . (\y . (\z . t))) a] b] c] -> Just ([(x, a), (y, b), (z, c)]) t)

[[(\x . t) a] b] -> Nothing -}
extractApps
  :: Term name uni fun a
  -> Maybe ([(UTermDef name uni fun a, a)], Term name uni fun a)
extractApps = go []
  where
    go argStack (Apply aa f arg) = go ((arg, aa) : argStack) f
    go argStack t = matchArgs argStack [] t
    matchArgs ((arg, aa) : rest) acc (LamAbs a n body) =
      matchArgs rest ((Def (UVarDecl a n) arg, aa) : acc) body
    matchArgs [] acc t =
      if null acc then Nothing else Just (reverse acc, t)
    matchArgs (_ : _) _ _ = Nothing

-- | The inverse of 'extractApps'.
restoreApps
  :: [(Either (Ann a) (UTermDef name uni fun (Ann a)), Ann a)]
  -> Term name uni fun (Ann a)
  -> Term name uni fun (Ann a)
restoreApps defs t = makeLams [] t (reverse defs)
  where
    -- `aa` is the annotation on the Apply node, and `al` is the annotation
    -- on the LamAbs node.
    makeLams args acc ((Left al, aa) : rest) =
      -- `Left` means the binding is dropped, so `acc` should be decorated with `al`.
      -- This corresponds to Note [Inliner's Certifier Hints], #3.
      makeLams ((Nothing, aa) : args) (decorateWith (al ^. decorations) acc) rest
    makeLams args acc ((Right (Def (UVarDecl al n) rhs), aa) : rest) =
      makeLams ((Just rhs, aa) : args) (LamAbs al n acc) rest
    makeLams args acc [] =
      makeApps args acc

    makeApps ((Nothing, aa) : args) acc =
      -- `Nothing` means the binding is dropped, so we decorate `acc with `aa` plus `DDrop`.
      -- This corresponds to Note [Inliner's Certifier Hints], #2.
      makeApps args (decorateWith (aa ^. decorations ++ [DDrop]) acc)
    makeApps ((Just arg, aa) : args) acc =
      makeApps args (Apply aa acc arg)
    makeApps [] acc = acc

-- | Run the inliner on a `UntypedPlutusCore.Core.Type.Term`.
processTerm
  :: forall name uni fun a
   . InliningConstraints name uni fun
  => Term name uni fun (Ann a)
  -> InlineM name uni fun a (Term name uni fun (Ann a))
processTerm = handleTerm
  where
    handleTerm
      :: Term name uni fun (Ann a)
      -> InlineM name uni fun a (Term name uni fun (Ann a))
    handleTerm = \case
      v@(Var a n) ->
        maybe
          v
          -- See Note [Inliner's Certifier Hints], #1
          (decorateWith (a ^. decorations) . decorateWith [DExpand])
          <$> substName n
      -- See Note [Differences from PIR inliner] 3
      (extractApps -> Just (bs, t)) -> do
        ebs <- traverse (processSingleBinding t) bs
        t' <- processTerm t
        pure $ restoreApps ebs t'
      t -> inlineSaturatedApp =<< forMOf termSubterms t processTerm

    -- See Note [Renaming strategy]
    substName :: name -> InlineM name uni fun a (Maybe (Term name uni fun (Ann a)))
    substName name = gets (lookupTerm name) >>= traverse renameTerm

    -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
    renameTerm
      :: InlineTerm name uni fun (Ann a)
      -> InlineM name uni fun a (Term name uni fun (Ann a))
    renameTerm = \case
      -- Already processed term, just rename and put it in, don't do any
      -- further optimization here.
      Done t -> liftDupable t

processSingleBinding
  :: InliningConstraints name uni fun
  => Term name uni fun (Ann a)
  -> (UTermDef name uni fun (Ann a), Ann a)
  -> InlineM name uni fun a (Either (Ann a) (UTermDef name uni fun (Ann a)), Ann a)
processSingleBinding body (Def vd@(UVarDecl a n) rhs0, aa) =
  (,aa) <$> do
    maybeAddSubst body (snd a) n rhs0 >>= \case
      Just rhs -> do
        let (binders, rhsBody) = UPLC.splitParams rhs
        modify' . extendVarInfo n $
          VarInfo
            { _varBinders = binders
            , _varRhs = rhs
            , _varRhsBody = Done (dupable rhsBody)
            }
        pure . Right $ Def vd rhs
      Nothing -> pure (Left a)

{-| Check against the heuristics we have for inlining and either inline
the term binding or not. The arguments to this function are the fields of the
'TermBinding' being processed.
Nothing means that we are inlining the term:
  * we have extended the substitution, and
  * we are removing the binding (hence we return Nothing). -}
maybeAddSubst
  :: forall name uni fun a
   . InliningConstraints name uni fun
  => Term name uni fun (Ann a)
  -> a
  -> name
  -> Term name uni fun (Ann a)
  -> InlineM name uni fun a (Maybe (Term name uni fun (Ann a)))
maybeAddSubst body a n rhs0 = do
  rhs <- processTerm rhs0

  -- Check whether we've been told specifically to inline this
  hints <- view iiHints
  case shouldInline hints a n of
    AlwaysInline ->
      -- if we've been told specifically, then do it right away
      extendAndDrop (Done $ dupable rhs)
    hint ->
      let safeToInline = hint == SafeToInline
       in ifM
            (shouldUnconditionallyInline safeToInline n rhs body)
            (extendAndDrop (Done $ dupable rhs))
            (pure $ Just rhs)
  where
    extendAndDrop
      :: forall b
       . InlineTerm name uni fun (Ann a)
      -> InlineM name uni fun a (Maybe b)
    extendAndDrop t = modify' (extendTerm n t) >> pure Nothing

shouldUnconditionallyInline
  :: InliningConstraints name uni fun
  => Bool
  {-^ Whether we know that the binding is safe to inline.
  If so, bypass the purity check. -}
  -> name
  -> Term name uni fun a
  -> Term name uni fun b
  -> InlineM name uni fun c Bool
shouldUnconditionallyInline safe n rhs body = do
  isTermPure <- checkPurity rhs
  inlineConstants <- view iiInlineConstants
  preUnconditional isTermPure ||^ postUnconditional inlineConstants isTermPure
  where
    -- similar to the paper, preUnconditional inlining checks that the binder
    -- is 'OnceSafe'.  I.e., it's used at most once AND it neither duplicate code
    -- or work. While we don't check for lambda etc like in the paper,
    -- 'effectSafe' ensures that it isn't doing any substantial work.
    -- We actually also inline 'Dead' binders (i.e., remove dead code) here.
    preUnconditional isTermPure =
      nameUsedAtMostOnce n &&^ (pure safe ||^ effectSafe body n isTermPure)
    -- See Note [Inlining approach and 'Secrets of the GHC Inliner'] and
    -- [Inlining and purity]. This is the case where we don't know that the number
    -- of occurrences is exactly one, so there's no point checking if the term is
    -- immediately evaluated.
    postUnconditional inlineConstants isTermPure =
      pure (safe || isTermPure) &&^ acceptable inlineConstants rhs

-- | Check if term is pure. See Note [Inlining and purity]
checkPurity
  :: PLC.ToBuiltinMeaning uni fun
  => Term name uni fun a
  -> InlineM name uni fun b Bool
checkPurity t = do
  builtinSemanticsVariant <- view iiBuiltinSemanticsVariant
  pure $ isPure builtinSemanticsVariant t

nameUsedAtMostOnce
  :: forall name uni fun a
   . InliningConstraints name uni fun
  => name
  -> InlineM name uni fun a Bool
nameUsedAtMostOnce n = do
  usgs <- view iiUsages
  -- 'inlining' terms used 0 times is a cheap way to remove dead code
  -- while we're here
  pure $ Usages.getUsageCount n usgs <= 1

isFirstVarBeforeEffects
  :: forall name uni fun ann
   . InliningConstraints name uni fun
  => BuiltinSemanticsVariant fun
  -> name
  -> Term name uni fun ann
  -> Bool
isFirstVarBeforeEffects builtinSemanticsVariant n t =
  -- This can in the worst case traverse a lot of the term, which could lead to
  -- us doing ~quadratic work as we process the program. However in practice
  -- most terms have a relatively short evaluation order before we hit Unknown,
  -- so it's not too bad.
  go (unEvalOrder (termEvaluationOrder builtinSemanticsVariant t))
  where
    -- Found the variable we're looking for!
    go ((EvalTerm _ _ (Var _ n')) : _) | n == n' = True
    -- Found a pure term, ignore it and continue
    go ((EvalTerm Pure _ _) : rest) = go rest
    -- Found a possibly impure term, our variable is definitely not first
    go ((EvalTerm MaybeImpure _ _) : _) = False
    -- Don't know, be conservative
    go (Unknown : _) = False
    go [] = False

{-| Check if the given name is strict in the given term.
  This means that at least one occurrence of the name is found outside of the following:
  * 'delay' term
  * lambda body
  * case branch -}
isStrictIn
  :: forall name uni fun a
   . Eq name
  => name
  -> Term name uni fun a
  -> Bool
isStrictIn name = go
  where
    go :: Term name uni fun a -> Bool
    go = \case
      Var _ann name' -> name == name'
      LamAbs _ann _paramName _body -> False
      Apply _ann t1 t2 -> go t1 || go t2
      Force _ann t -> go t
      Delay _ann _term -> False
      Constant {} -> False
      Builtin {} -> False
      Error {} -> False
      Constr _ann _idx terms -> any go terms
      Case _ann scrut _branches -> go scrut

effectSafe
  :: forall name uni fun a b
   . InliningConstraints name uni fun
  => Term name uni fun a
  -> name
  -> Bool
  -- ^ is it pure? See Note [Inlining and purity]
  -> InlineM name uni fun b Bool
effectSafe body n termIsPure = do
  preserveLogging <- view iiPreserveLogging
  builtinSemantics <- view iiBuiltinSemanticsVariant
  return $
    termIsPure
      || isFirstVarBeforeEffects builtinSemantics n body
      || (not preserveLogging && isStrictIn n body)

{-| Should we inline? Should only inline things that won't duplicate work
or code.  See Note [Inlining approach and 'Secrets of the GHC Inliner'] -}
acceptable
  :: Bool
  -- ^ inline constants
  -> Term name uni fun a
  -> InlineM name uni fun b Bool
acceptable inlineConstants t =
  -- See Note [Inlining criteria]
  pure $ costIsAcceptable t && sizeIsAcceptable inlineConstants t

{-| Is the cost increase (in terms of evaluation work) of inlining a variable
whose RHS is the given term acceptable? -}
costIsAcceptable :: Term name uni fun a -> Bool
costIsAcceptable = \case
  Builtin {} -> True
  Var {} -> True
  Constant {} -> True
  Error {} -> True
  -- This will mean that we create closures at each use site instead of
  -- once, but that's a very low cost which we're okay rounding to 0.
  LamAbs {} -> True
  Apply {} -> False
  -- Inlining constructors of size 1 or 0 seems okay, but does result in doing
  -- the work for the elements at each use site.
  Constr _ _ es ->
    case es of
      [] -> True
      [e] -> costIsAcceptable e
      _ -> False
  -- Inlining a case means redoing the match at each use site
  Case {} -> False
  Force {} -> False
  Delay {} -> True

{-| Is the size increase (in the AST) of inlining a variable whose RHS is
the given term acceptable? -}
sizeIsAcceptable
  :: Bool
  -- ^ inline constants
  -> Term name uni fun a
  -> Bool
sizeIsAcceptable inlineConstants = \case
  Builtin {} -> True
  Var {} -> True
  Error {} -> True
  -- See Note [Differences from PIR inliner] 4
  LamAbs {} -> False
  -- Inlining constructors of size 1 or 0 seems okay
  Constr _ _ es -> case es of
    [] -> True
    [e] -> sizeIsAcceptable inlineConstants e
    _ -> False
  -- Cases are pretty big, due to the case branches
  Case {} -> False
  -- Inlining constants is deemed acceptable if the 'inlineConstants'
  -- flag is turned on, see Note [Inlining constants].
  Constant {} -> inlineConstants
  Apply {} -> False
  Force _ t -> sizeIsAcceptable inlineConstants t
  Delay _ t -> sizeIsAcceptable inlineConstants t

-- | Fully apply and beta reduce.
fullyApplyAndBetaReduce
  :: forall name uni fun a
   . InliningConstraints name uni fun
  => Ann a
  -- ^ Annotation on the variable to be replaced
  -> VarInfo name uni fun (Ann a)
  -> [(Ann a, Term name uni fun (Ann a))]
  -> InlineM name uni fun a (Maybe (Term name uni fun (Ann a)))
fullyApplyAndBetaReduce av info args0 = do
  rhsBody <-
    -- Since we would like to fully apply here, we add decorations to
    -- `rhsBody` in the following order:
    --
    --   * decorations on the outermost Apply node, plus DDrop
    --   * decorations on the next Apply node, plus DDrop
    --   * ...
    --   * decorations on the innermost Apply node, plus DDrop
    --   * `av` plus DExpand.
    --   * decorations on the first LamAbs
    --   * decorations on the second LamAbs
    --   * ...
    --   * decorations on the last LamAbs
    --
    -- See Note [Inliner's Certifier Hints].
    decorateWith
      ( concatMap (\(annApply, _arg) -> annApply ^. decorations ++ [DDrop]) (reverse args0)
          ++ av ^. decorations
          ++ [DExpand]
          ++ concatMap (\(_name, annLam) -> annLam ^. decorations) (info ^. varBinders)
      )
      <$> liftDupable (let Done rhsBody = info ^. varRhsBody in rhsBody)
  let go
        :: Term name uni fun (Ann a)
        -> [(name, Ann a)]
        -> [(Ann a, Term name uni fun (Ann a))]
        -> InlineM name uni fun a (Maybe (Term name uni fun (Ann a)))
      go acc bs args = case (bs, args) of
        ([], _) -> pure . Just $ mkIterApp acc args
        ((param, _annLam) : params, (_annArg, arg) : args') -> do
          safe <- safeToBetaReduce param arg
          if safe
            then do
              acc' <-
                termSubstNamesM
                  ( \n a ->
                      if n == param
                        then
                          Just
                            -- See Note [Inliner's Certifier Hints], #1
                            . decorateWith (a ^. decorations)
                            . decorateWith [DExpand]
                            <$> PLC.rename arg
                        else pure Nothing
                  )
                  acc
              go acc' params args'
            else pure Nothing
        _ -> pure Nothing

      -- Is it safe to turn `(\a -> body) arg` into `body [a := arg]`?
      -- The criteria is the same as the criteria for unconditionally
      -- inlining `a`, since inlining is the same as beta reduction.
      safeToBetaReduce
        :: name
        -> Term name uni fun (Ann a)
        -> InlineM name uni fun a Bool
      safeToBetaReduce a arg = shouldUnconditionallyInline False a arg rhsBody
  go rhsBody (info ^. varBinders) args0

{-| This works in the same way as
'PlutusIR.Transform.Inline.CallSiteInline.inlineSaturatedApp'.
See Note [Inlining and beta reduction of functions]. -}
inlineSaturatedApp
  :: forall name uni fun a
   . InliningConstraints name uni fun
  => Term name uni fun (Ann a)
  -> InlineM name uni fun a (Term name uni fun (Ann a))
inlineSaturatedApp t
  | (Var av name, args) <- UPLC.splitApplication t =
      gets (lookupVarInfo name) >>= \case
        Nothing -> pure t
        Just varInfo ->
          fullyApplyAndBetaReduce av varInfo args >>= \case
            Nothing -> pure t
            Just fullyApplied -> do
              thresh <- view iiInlineCallsiteGrowth
              let
                -- Inline only if the size is no bigger than
                -- not inlining plus threshold.
                sizeIsOk =
                  termAstSize fullyApplied <= termAstSize t + max 0 thresh
                rhs = varInfo ^. varRhs
                -- Cost is always OK if the RHS is a LamAbs,
                -- but may not be otherwise.
                costIsOk = costIsAcceptable rhs
              -- The RHS is always pure if it is a LamAbs,
              -- but may not be otherwise.
              rhsPure <- checkPurity rhs
              pure $
                if sizeIsOk && costIsOk && rhsPure
                  then fullyApplied
                  else t
  | otherwise = pure t

-------------------------------------------------------------------------------
-- The following are types and functions for producing certifier hints.
-- See Note [Inliner's Certifier Hints] for an overview.
-------------------------------------------------------------------------------

-- | An enclosing Drop or Expand layer
data Decoration = DDrop | DExpand

type Ann a = ([Decoration], a)

emptyDecoration :: a -> Ann a
emptyDecoration = (mempty,)
{-# INLINE emptyDecoration #-}

decorations :: Lens' (Ann a) [Decoration]
decorations = _1
{-# INLINE decorations #-}

-- | Prepend the given decorations
decorateWith :: [Decoration] -> Term name uni fun (Ann a) -> Term name uni fun (Ann a)
decorateWith ds = modifyTermAnn (first (ds ++))
{-# INLINE decorateWith #-}

-- | Fold a decorated term into certifier hints.
mkHints :: Term name uni fun (Ann a) -> CertifierHints.Inline
mkHints = go
  where
    go t = decorate hints ds
      where
        decorate :: CertifierHints.Inline -> [Decoration] -> CertifierHints.Inline
        decorate = foldr $ \d h -> case d of
          DDrop -> CertifierHints.InlDrop h
          DExpand -> CertifierHints.InlExpand h

        ds = termAnn t ^. decorations

        hints = case t of
          Var {} -> CertifierHints.InlVar
          LamAbs _ _ body -> CertifierHints.InlLam (go body)
          Apply _ fun arg -> CertifierHints.InlApply (go fun) (go arg)
          Force _ body -> CertifierHints.InlForce (go body)
          Delay _ body -> CertifierHints.InlDelay (go body)
          Constant {} -> CertifierHints.InlCon
          Builtin {} -> CertifierHints.InlBuiltin
          Error {} -> CertifierHints.InlError
          Constr _ _ args -> CertifierHints.InlConstr (go <$> args)
          Case _ scrut alts -> CertifierHints.InlCase (go scrut) (go <$> V.toList alts)

{- Note [Inliner's Certifier Hints]

To certify the inliner, the certifier requires the inliner to emit hints that record
where inlining operations occur. These hints are represented by the `Inline` data type
defined in `UntypedPlutusCore.Transform.Certify.Hints`.

Given a pre-term and a post-term, the expected hints can be defined by viewing the
inliner as a process that repeatedly performs one of the following two operations:

1. Substituting a term for a variable
2. Dropping a dead binding

Certifier hints are then defined constructively according to the following procedure.
In the end, the final hints mirror the post-term structure, except that each node may be
decorated with an arbitrary number of `InlDrop` or `InlExpand` layers, reflecting the
inlining operations that the inliner has performed.

- Initially the hints mirror the pre-term structure, using constructors of `Inline`
  except `InlExpand` and `InlDrop`. Excluding these two constructors, there is a
  1-1 correspondence between hints constructors and AST constructors.

- Suppose the inliner performs operation 1, substituting term `N` for variable `v`.
  Before the substitution, we have

    hints(v) = decorations(InlVar)

  where `decorations` denotes an arbitrary number of enclosing `InlDrop` or `InlExpand`
  layers. After the substitution, the hints at this location should become

    decorations(InlExpand hints(N))                         (#1)

  In other words, `InlVar` is replaced by `hints(N)` wrapped in an additional `InlExpand`.

- Suppose the inliner performs operation 2, turning `(\x‾ₙ y. M) X‾ₙ Y` into `(\x‾ₙ. M) X‾ₙ`,
  where `x‾ₙ` and `X‾ₙ` denote sequences `x₁ x₂ ... xₙ` and `X₁ X₂ ... Xₙ` with `n >= 0`.
  Before this, we have

    hints((\x‾ₙ y. M) X‾ₙ Y) = decorations₁(InlApply (hints((\x‾ₙ y. M) X‾ₙ)) (hints(Y)))
    hints(\y. M) = decorations₂(InlLam hints(M))

  Afterwards, the hints for `(\x‾ₙ y. M) X‾ₙ` should become

    decorations₁(InlDrop (hints((\x‾ₙ y. M) X‾ₙ)))           (#2)

  That is, it is decorated with `decorations₁` plus `InlDrop`.
  The hints for `M` should become

    decorations₂(hints(M))                                   (#3)

  That is, it is decorated with `decorations₂`. Note that when `n = 0`,
  `(\x‾ₙ y. M) X‾ₙ` becomes `M`, and therefore, `hints(M)` should be decorated with
  `decorations₁` plus `InlDrop` plus `decorations₂`.

Refer to the golden tests for examples of hints (look for files ending with
`.golden.certifier-hints`).

Implementing this is quite fiddly, but is still easier than it sounds from the above
description. Observe that at any point during inlining, the hints structure mirrors
the structure of the current term, except for the decorations. Therefore all we need
is to store the decorations of each node in its `ann`. When inlining is done, we can
construct the hints structure using these decorations.
-}
