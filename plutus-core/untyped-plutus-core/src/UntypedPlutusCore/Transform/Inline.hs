{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE ViewPatterns     #-}

{-| An inlining pass.

This pass is essentially a copy of the PIR inliner, and should be KEPT IN SYNC
with it. It's hard to do this with true abstraction, so we just have to keep
two copies reasonably similar.

However, there are some differences. In the interests of making it easier
to keep things in sync, these are explicitly listed in
Note [Differences from PIR inliner]. If you add another difference,
please note it there! Obviously fewer differences is better.

See Note [The problem of inlining destructors] for why this pass exists.
-}
module UntypedPlutusCore.Transform.Inline (
  inline,
  InlineHints (..),

  -- * Exported for testing
  InlineM,
  S (..),
  InlineInfo (..),
  Subst (..),
  TermEnv (..),
  isFirstVarBeforeEffects,
  isStrictIn,
  effectSafe,
) where

import Control.Lens (forMOf, makeLenses, view, (%~), (&), (^.))
import Control.Monad.Extra (ifM, (&&^), (||^))
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State (StateT, evalStateT, gets, modify')
import PlutusCore qualified as PLC
import PlutusCore.Annotation (Inline (AlwaysInline, SafeToInline), InlineHints (..))
import PlutusCore.Builtin (ToBuiltinMeaning (BuiltinSemanticsVariant))
import PlutusCore.Builtin qualified as PLC
import PlutusCore.MkPlc (mkIterApp)
import PlutusCore.Name.Unique (HasUnique, TermUnique (..), Unique (..))
import PlutusCore.Name.UniqueMap qualified as UMap
import PlutusCore.Quote (MonadQuote (..), Quote)
import PlutusCore.Rename (Dupable, dupable, liftDupable)
import PlutusPrelude (Generic, fromMaybe)
import UntypedPlutusCore.Analysis.Usages qualified as Usages
import UntypedPlutusCore.Core qualified as UPLC
import UntypedPlutusCore.Core.Plated (termSubterms)
import UntypedPlutusCore.Core.Type (Term (..), termAnn)
import UntypedPlutusCore.MkUPlc (Def (..), UTermDef, UVarDecl (..))
import UntypedPlutusCore.Purity (EvalTerm (EvalTerm, Unknown), Purity (MaybeImpure, Pure), isPure,
                                 termEvaluationOrder, unEvalOrder)
import UntypedPlutusCore.Rename ()
import UntypedPlutusCore.AstSize (AstSize, termAstSize)
import UntypedPlutusCore.Subst (termSubstNamesM)
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (Inline), SimplifierT,
                                               recordSimplification)
import Witherable (wither)

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
A map of unprocessed variable and its substitution range.
-}
newtype TermEnv name uni fun a = TermEnv
  {_unTermEnv :: PLC.UniqueMap TermUnique (InlineTerm name uni fun a)}
  deriving newtype (Semigroup, Monoid)

{-| Wrapper of term substitution so that it's similar to the PIR inliner.
See Note [Differences from PIR inliner] 1
-}
newtype Subst name uni fun a = Subst {_termEnv :: TermEnv name uni fun a}
  deriving stock (Generic)
  deriving newtype (Semigroup, Monoid)

makeLenses ''TermEnv
makeLenses ''Subst

data VarInfo name uni fun ann = VarInfo
  { _varBinders :: [name]
  -- ^ Lambda binders in the RHS (definition) of the variable.
  , _varRhs     :: Term name uni fun ann
  -- ^ The RHS (definition) of the variable.
  , _varRhsBody :: InlineTerm name uni fun ann
  {- ^ The body of the RHS of the variable (i.e., RHS minus the binders).
  Using 'InlineTerm' here to ensure the body is renamed when inlined.
  -}
  }

makeLenses ''VarInfo

-- | UPLC inliner state
data S name uni fun a = S
  { _subst :: Subst name uni fun a
  , _vars  :: PLC.UniqueMap TermUnique (VarInfo name uni fun a)
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
  { _iiUsages                  :: Usages.Usages
  , _iiHints                   :: InlineHints name a
  , _iiBuiltinSemanticsVariant :: PLC.BuiltinSemanticsVariant fun
  , _iiInlineConstants         :: Bool
  , _iiInlineCallsiteGrowth    :: AstSize
  , _iiPreserveLogging         :: Bool
  }

makeLenses ''InlineInfo

-- Using a concrete monad makes a very large difference to the performance
-- of this module (determined from profiling)

-- | The monad the inliner runs in.
type InlineM name uni fun a =
  ReaderT (InlineInfo name fun a) (StateT (S name uni fun a) Quote)

-- | Look up the unprocessed variable in the substitution.
lookupTerm
  :: (HasUnique name TermUnique)
  => name
  -> S name uni fun a
  -> Maybe (InlineTerm name uni fun a)
lookupTerm n s = UMap.lookupName n $ s ^. subst . termEnv . unTermEnv

-- | Insert the unprocessed variable into the substitution.
extendTerm
  :: (HasUnique name TermUnique)
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
  :: (HasUnique name TermUnique)
  => name
  -> S name uni fun a
  -> Maybe (VarInfo name uni fun a)
lookupVarInfo n s = UMap.lookupName n $ s ^. vars

extendVarInfo
  :: (HasUnique name TermUnique)
  => name
  -> VarInfo name uni fun a
  -> S name uni fun a
  -> S name uni fun a
extendVarInfo n info s = s & vars %~ UMap.insertByName n info

{-| Inline simple bindings. Relies on global uniqueness, and preserves it.
See Note [Inlining and global uniqueness]
-}
inline
  :: forall name uni fun m a
   . (ExternalConstraints name uni fun m)
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
    result <-
      liftQuote $
        flip evalStateT mempty $
          runReaderT
            (processTerm t)
            InlineInfo
              { _iiUsages = Usages.termUsages t
              , _iiHints = hints
              , _iiBuiltinSemanticsVariant = builtinSemanticsVariant
              , _iiInlineConstants = inlineConstants
              , _iiInlineCallsiteGrowth = callsiteGrowth
              , _iiPreserveLogging = preserveLogging
              }
    recordSimplification t Inline result
    return result

-- See Note [Differences from PIR inliner] 3

{-| Extract the list of applications from a term,
a bit like a "multi-beta" reduction.

Some examples will help:
[(\x . t) a] -> Just ([(x, a)], t)

[[[(\x . (\y . (\z . t))) a] b] c] -> Just ([(x, a), (y, b), (z, c)]) t)

[[(\x . t) a] b] -> Nothing
-}
extractApps
  :: Term name uni fun a
  -> Maybe ([UTermDef name uni fun a], Term name uni fun a)
extractApps = go []
 where
  go argStack (Apply _ f arg) = go (arg : argStack) f
  go argStack t               = matchArgs argStack [] t
  matchArgs (arg : rest) acc (LamAbs a n body) =
    matchArgs rest (Def (UVarDecl a n) arg : acc) body
  matchArgs [] acc t =
    if null acc then Nothing else Just (reverse acc, t)
  matchArgs (_ : _) _ _ = Nothing

-- | The inverse of 'extractApps'.
restoreApps
  :: [UTermDef name uni fun a]
  -> Term name uni fun a
  -> Term name uni fun a
restoreApps defs t = makeLams [] t (reverse defs)
 where
  makeLams args acc (Def (UVarDecl a n) rhs : rest) =
    makeLams (rhs : args) (LamAbs a n acc) rest
  makeLams args acc [] =
    makeApps args acc
  -- This isn't the best annotation, but it will do
  makeApps (arg : args) acc =
    makeApps args (Apply (termAnn acc) acc arg)
  makeApps [] acc = acc

-- | Run the inliner on a `UntypedPlutusCore.Core.Type.Term`.
processTerm
  :: forall name uni fun a
   . (InliningConstraints name uni fun)
  => Term name uni fun a
  -> InlineM name uni fun a (Term name uni fun a)
processTerm = handleTerm
 where
  handleTerm
    :: Term name uni fun a
    -> InlineM name uni fun a (Term name uni fun a)
  handleTerm = \case
    v@(Var _ n) -> fromMaybe v <$> substName n
    -- See Note [Differences from PIR inliner] 3
    (extractApps -> Just (bs, t)) -> do
      bs' <- wither (processSingleBinding t) bs
      t' <- processTerm t
      pure $ restoreApps bs' t'
    t -> inlineSaturatedApp =<< forMOf termSubterms t processTerm

  -- See Note [Renaming strategy]
  substName :: name -> InlineM name uni fun a (Maybe (Term name uni fun a))
  substName name = gets (lookupTerm name) >>= traverse renameTerm

  -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
  renameTerm
    :: InlineTerm name uni fun a
    -> InlineM name uni fun a (Term name uni fun a)
  renameTerm = \case
    -- Already processed term, just rename and put it in, don't do any
    -- further optimization here.
    Done t -> liftDupable t

processSingleBinding
  :: (InliningConstraints name uni fun)
  => Term name uni fun a
  -> UTermDef name uni fun a
  -> InlineM name uni fun a (Maybe (UTermDef name uni fun a))
processSingleBinding body (Def vd@(UVarDecl a n) rhs0) = do
  maybeAddSubst body a n rhs0 >>= \case
    Just rhs -> do
      let (binders, rhsBody) = UPLC.splitParams rhs
      modify' . extendVarInfo n $
        VarInfo
          { _varBinders = binders
          , _varRhs = rhs
          , _varRhsBody = Done (dupable rhsBody)
          }
      pure . Just $ Def vd rhs
    Nothing -> pure Nothing

{-| Check against the heuristics we have for inlining and either inline
the term binding or not. The arguments to this function are the fields of the
'TermBinding' being processed.
Nothing means that we are inlining the term:
  * we have extended the substitution, and
  * we are removing the binding (hence we return Nothing).
-}
maybeAddSubst
  :: forall name uni fun a
   . (InliningConstraints name uni fun)
  => Term name uni fun a
  -> a
  -> name
  -> Term name uni fun a
  -> InlineM name uni fun a (Maybe (Term name uni fun a))
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
     . InlineTerm name uni fun a
    -> InlineM name uni fun a (Maybe b)
  extendAndDrop t = modify' (extendTerm n t) >> pure Nothing

shouldUnconditionallyInline
  :: (InliningConstraints name uni fun)
  => Bool
  {- ^ Whether we know that the binding is safe to inline.
  If so, bypass the purity check.
  -}
  -> name
  -> Term name uni fun a
  -> Term name uni fun a
  -> InlineM name uni fun a Bool
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
  :: (PLC.ToBuiltinMeaning uni fun)
  => Term name uni fun a
  -> InlineM name uni fun a Bool
checkPurity t = do
  builtinSemanticsVariant <- view iiBuiltinSemanticsVariant
  pure $ isPure builtinSemanticsVariant t

nameUsedAtMostOnce
  :: forall name uni fun a
   . (InliningConstraints name uni fun)
  => name
  -> InlineM name uni fun a Bool
nameUsedAtMostOnce n = do
  usgs <- view iiUsages
  -- 'inlining' terms used 0 times is a cheap way to remove dead code
  -- while we're here
  pure $ Usages.getUsageCount n usgs <= 1

isFirstVarBeforeEffects
  :: forall name uni fun ann
   . (InliningConstraints name uni fun)
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
  * case branch
-}
isStrictIn
  :: forall name uni fun a
   . (Eq name)
  => name
  -> Term name uni fun a
  -> Bool
isStrictIn name = go
 where
  go :: Term name uni fun a -> Bool
  go = \case
    Var _ann name' -> name == name'
    LamAbs _ann _paramName _body -> False
    Let _ann _names _body -> False
    Apply _ann t1 t2 -> go t1 || go t2
    Bind _ann body binds -> go body || any go binds
    Force _ann t -> go t
    Delay _ann _term -> False
    Constant{} -> False
    Builtin{} -> False
    Error{} -> False
    Constr _ann _idx terms -> any go terms
    Case _ann scrut _branches -> go scrut

effectSafe
  :: forall name uni fun a
   . (InliningConstraints name uni fun)
  => Term name uni fun a
  -> name
  -> Bool
  -- ^ is it pure? See Note [Inlining and purity]
  -> InlineM name uni fun a Bool
effectSafe body n termIsPure = do
  preserveLogging <- view iiPreserveLogging
  builtinSemantics <- view iiBuiltinSemanticsVariant
  return $
    termIsPure
      || isFirstVarBeforeEffects builtinSemantics n body
      || (not preserveLogging && isStrictIn n body)

{-| Should we inline? Should only inline things that won't duplicate work
or code.  See Note [Inlining approach and 'Secrets of the GHC Inliner']
-}
acceptable
  :: Bool
  -- ^ inline constants
  -> Term name uni fun a
  -> InlineM name uni fun a Bool
acceptable inlineConstants t =
  -- See Note [Inlining criteria]
  pure $ costIsAcceptable t && sizeIsAcceptable inlineConstants t

{-| Is the cost increase (in terms of evaluation work) of inlining a variable
whose RHS is the given term acceptable?
-}
costIsAcceptable :: Term name uni fun a -> Bool
costIsAcceptable = \case
  Builtin{} -> True
  Var{} -> True
  Constant{} -> True
  Error{} -> True
  -- This will mean that we create closures at each use site instead of
  -- once, but that's a very low cost which we're okay rounding to 0.
  LamAbs{} -> True
  Apply{} -> False
  -- Inlining constructors of size 1 or 0 seems okay, but does result in doing
  -- the work for the elements at each use site.
  Constr _ _ es ->
    case es of
      []  -> True
      [e] -> costIsAcceptable e
      _   -> False
  -- Inlining a case means redoing the match at each use site
  Case{} -> False
  Force{} -> False
  Delay{} -> True
  Bind{} -> False
  Let{} -> False

{-| Is the size increase (in the AST) of inlining a variable whose RHS is
the given term acceptable?
-}
sizeIsAcceptable
  :: Bool
  -- ^ inline constants
  -> Term name uni fun a
  -> Bool
sizeIsAcceptable inlineConstants = \case
  Builtin{} -> True
  Var{} -> True
  Error{} -> True
  -- See Note [Differences from PIR inliner] 4
  LamAbs{} -> False
  -- Inlining constructors of size 1 or 0 seems okay
  Constr _ _ es -> case es of
    []  -> True
    [e] -> sizeIsAcceptable inlineConstants e
    _   -> False
  -- Cases are pretty big, due to the case branches
  Case{} -> False
  -- Inlining constants is deemed acceptable if the 'inlineConstants'
  -- flag is turned on, see Note [Inlining constants].
  Constant{} -> inlineConstants
  Apply{} -> False
  Force _ t -> sizeIsAcceptable inlineConstants t
  Delay _ t -> sizeIsAcceptable inlineConstants t

-- | Fully apply and beta reduce.
fullyApplyAndBetaReduce
  :: forall name uni fun a
   . (InliningConstraints name uni fun)
  => VarInfo name uni fun a
  -> [(a, Term name uni fun a)]
  -> InlineM name uni fun a (Maybe (Term name uni fun a))
fullyApplyAndBetaReduce info args0 = do
  rhsBody <- liftDupable (let Done rhsBody = info ^. varRhsBody in rhsBody)
  let go
        :: Term name uni fun a
        -> [name]
        -> [(a, Term name uni fun a)]
        -> InlineM name uni fun a (Maybe (Term name uni fun a))
      go acc bs args = case (bs, args) of
        ([], _) -> pure . Just $ mkIterApp acc args
        (param : params, (_ann, arg) : args') -> do
          safe <- safeToBetaReduce param arg
          if safe
            then do
              acc' <-
                termSubstNamesM
                  ( \n ->
                      if n == param
                        then Just <$> PLC.rename arg
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
        -> Term name uni fun a
        -> InlineM name uni fun a Bool
      safeToBetaReduce a arg = shouldUnconditionallyInline False a arg rhsBody
  go rhsBody (info ^. varBinders) args0

{-| This works in the same way as
'PlutusIR.Transform.Inline.CallSiteInline.inlineSaturatedApp'.
See Note [Inlining and beta reduction of functions].
-}
inlineSaturatedApp
  :: forall name uni fun a
   . (InliningConstraints name uni fun)
  => Term name uni fun a
  -> InlineM name uni fun a (Term name uni fun a)
inlineSaturatedApp t
  | (Var _ann name, args) <- UPLC.splitApplication t =
      gets (lookupVarInfo name) >>= \case
        Nothing -> pure t
        Just varInfo ->
          fullyApplyAndBetaReduce varInfo args >>= \case
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
