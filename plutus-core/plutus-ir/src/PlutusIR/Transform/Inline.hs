{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}
{-|
An inlining pass.

Note that there is (essentially) a copy of this in the UPLC inliner, and the two
should be KEPT IN SYNC, so if you make changes here please either make them in the other
one too or add to the comment that summarises the differences.
-}
module PlutusIR.Transform.Inline (inline, InlineHints (..)) where

import PlutusIR
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.MkPir (mkLet)
import PlutusIR.Purity (isPure)
import PlutusIR.Transform.Rename ()
import PlutusPrelude

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.InlineUtils
import PlutusCore.Name
import PlutusCore.Quote
import PlutusCore.Rename (Dupable, dupable, liftDupable)
import PlutusCore.Subst (typeSubstTyNamesM)

import Control.Lens hiding (Strict)
import Control.Monad.Reader
import Control.Monad.State

import Algebra.Graph qualified as G
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Witherable (Witherable (wither))

{- Note [Inlining approach and 'Secrets of the GHC Inliner']
The approach we take is more-or-less exactly taken from 'Secrets of the GHC Inliner'.

Overall, the cause of differences is that we are largely trying to just clean up some
basic issues, not do serious optimization. In many cases we've already run the GHC simplifier
on our input!

We differ from the paper a few ways, mostly leaving things out:

Functionality
------------

CallSiteInline: TODO in PLT-1146

Inlining recursive bindings: not worth it, complicated.

Context-based inlining: TODO

Beta-reduction: done in `Beta.hs`, not here.

Implementation
--------------

In-scope set: we don't bother keeping it, since we only ever substitute in things that
don't have bound variables.

Suspended substitutions ('SuspEx') for values: we don't need it, because we simplify the RHS before
preInlineUnconditional. For GHC, they can do more simplification in context, but they only want to
process the binding RHS once, so delaying it until the call site is better
if it's a single-occurrence term. But in our case it's fine to leave any improved in-context
simplification to later passes, so we don't need this complication.

Optimization after substituting in DoneExprs: we can't make different inlining decisions
contextually, so there's no point doing this.
-}

{- Note [The problem of inlining destructors]
Destructors are *perfect* candidates for inlining:

1. They are *always* called fully-saturated, because they are created from pattern matches,
which always provide all the arguments.
2. They will reduce well after being inlined, since their bodies consist of just one argument
applied to the others.

Unfortunately, we can't inline them even after we've eliminated datatypes, because they look like
this (see Note [Abstract data types]):

(/\ ty :: * .
  ...
  -- ty abstract
  \match : <destructor type> .
    <user term>
)
<defn of ty>
...
-- ty concrete
<defn of match>

This doesn't look like a let-binding because there is a type abstraction in between the lambda
and its argument! And this abstraction is important: the body of the matcher only typechecks
if it is *outside* the type abstraction, so we can't just push it inside or something.

We *could* inline 'ty', but this way lies madness: doing that consistently would mean inlining
the definitions of *all* datatypes, which would enormously (exponentially!) bloat the types
inside, making the typechecker (and everything else that processes the AST) incredibly slow.

So it seems that we're stuck. We can't inline destructors in PIR.

But we *can* do it in UPLC! No types, so no problem. The type abstraction/instantiation will
turn into a delay/force pair and get simplified away, and then we have something that we can
inline. This is essentially the reason for the existence of the UPLC inlining pass.
-}

-- | Substitution range, 'SubstRng' in the paper but no 'Susp' case.
-- See Note [Inlining approach and 'Secrets of the GHC Inliner']
newtype InlineTerm tyname name uni fun a =
    Done (Dupable (Term tyname name uni fun a)) --out expressions

-- | Term substitution, 'Subst' in the paper.
-- A map of unprocessed variable and its substitution range.
newtype TermEnv tyname name uni fun a =
    TermEnv { _unTermEnv :: UniqueMap TermUnique (InlineTerm tyname name uni fun a) }
    deriving newtype (Semigroup, Monoid)

-- | Type substitution, similar to `TermEnv` but for types.
-- A map of unprocessed type variable and its substitution range.
newtype TypeEnv tyname uni a =
    TypeEnv { _unTypeEnv :: UniqueMap TypeUnique (Dupable (Type tyname uni a)) }
    deriving newtype (Semigroup, Monoid)

-- | Substitution for both terms and types.
-- Similar to 'Subst' in the paper, but the paper only has terms.
data Subst tyname name uni fun a = Subst { _termEnv :: TermEnv tyname name uni fun a
                                         , _typeEnv :: TypeEnv tyname uni a
                                         }
    deriving stock (Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (Subst tyname name uni fun a))

makeLenses ''TermEnv
makeLenses ''TypeEnv
makeLenses ''Subst

type ExternalConstraints tyname name uni fun m =
    ( HasUnique name TermUnique
    , HasUnique tyname TypeUnique
    , Eq name
    , PLC.ToBuiltinMeaning uni fun
    , MonadQuote m
    )

type InliningConstraints tyname name uni fun =
    ( HasUnique name TermUnique
    , HasUnique tyname TypeUnique
    , Eq name
    , PLC.ToBuiltinMeaning uni fun
    )

data InlineInfo name fun a = InlineInfo
    { _iiStrictnessMap :: Deps.StrictnessMap
    -- ^ Is it strict? Only needed for PIR, not UPLC
    , _iiUsages        :: Usages.Usages
    -- ^ how many times is it used?
    , _iiHints         :: InlineHints name a
    -- ^ have we explicitly been told to inline.
    , _iiBuiltinVer    :: PLC.BuiltinVersion fun
    -- ^ the builtin version.
    }
makeLenses ''InlineInfo

-- Using a concrete monad makes a very large difference to the performance of this module
-- (determined from profiling)
-- | The monad the inliner runs in.
type InlineM tyname name uni fun a =
    ReaderT (InlineInfo name fun a) (StateT (Subst tyname name uni fun a) Quote)

-- | Look up the unprocessed variable in the substitution.
lookupTerm
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> Subst tyname name uni fun a -- ^ The substitution.
    -> Maybe (InlineTerm tyname name uni fun a)
lookupTerm n subst = lookupName n $ subst ^. termEnv . unTermEnv

-- | Insert the unprocessed variable into the substitution.
extendTerm
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> InlineTerm tyname name uni fun a -- ^ The substitution range.
    -> Subst tyname name uni fun a -- ^ The substitution.
    -> Subst tyname name uni fun a
extendTerm n clos subst = subst & termEnv . unTermEnv %~ insertByName n clos

-- | Look up the unprocessed type variable in the substitution.
lookupType
    :: (HasUnique tyname TypeUnique)
    => tyname
    -> Subst tyname name uni fun a
    -> Maybe (Dupable (Type tyname uni a))
lookupType tn subst = lookupName tn $ subst ^. typeEnv . unTypeEnv

-- | Check if the type substitution is empty.
isTypeSubstEmpty :: Subst tyname name uni fun a -> Bool
isTypeSubstEmpty (Subst _ (TypeEnv tyEnv)) = isEmpty tyEnv

-- | Insert the unprocessed type variable into the substitution.
extendType
    :: (HasUnique tyname TypeUnique)
    => tyname -- ^ The name of the type variable.
    -> Type tyname uni a -- ^ Its type.
    -> Subst tyname name uni fun a -- ^ The substitution.
    -> Subst tyname name uni fun a
extendType tn ty subst = subst &  typeEnv . unTypeEnv %~ insertByName tn (dupable ty)

{- Note [Inlining and global uniqueness]
Inlining relies on global uniqueness (we store things in a unique map), and *does* currently
preserve it because we don't currently inline anything with binders.

If we do start inlining things with binders in them, we should probably try and preserve it by
doing something like 'The rapier' section from the paper. We could also just bite the bullet
and rename everything when we substitute in, which GHC considers too expensive but we might accept.
-}

-- | Inline simple bindings. Relies on global uniqueness, and preserves it.
-- See Note [Inlining and global uniqueness]
inline
    :: forall tyname name uni fun a m
    . ExternalConstraints tyname name uni fun m
    => InlineHints name a
    -> PLC.BuiltinVersion fun
    -> Term tyname name uni fun a
    -> m (Term tyname name uni fun a)
inline hints ver t = let
        inlineInfo :: InlineInfo name fun a
        inlineInfo = InlineInfo (snd deps) usgs hints ver
        -- We actually just want the variable strictness information here!
        deps :: (G.Graph Deps.Node, Map.Map PLC.Unique Strictness)
        deps = Deps.runTermDeps ver t
        usgs :: Usages.Usages
        usgs = Usages.termUsages t
    in liftQuote $ flip evalStateT mempty $ flip runReaderT inlineInfo $ processTerm t

{- Note [Removing inlined bindings]
We *do* remove bindings that we inline (since we only do unconditional inlining). We *could*
leave this to the dead code pass, but it's helpful to do it here.
Crucially, we have to do the same reasoning wrt strict bindings and purity
(see Note [Inlining and purity]):
we can only inline *pure* strict bindings, which is effectively the same as what we do in the dead
code pass.

Annoyingly, this requires us to redo the analysis that we do for the dead binding pass.
TODO: merge them or figure out a way to share more work, especially since there's similar logic.
This might mean reinventing GHC's OccAnal...
-}

-- | Run the inliner on a `Core.Type.Term`.
processTerm
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Term tyname name uni fun a -- ^ Term to be processed.
    -> InlineM tyname name uni fun a (Term tyname name uni fun a)
processTerm = handleTerm <=< traverseOf termSubtypes applyTypeSubstitution where
    handleTerm ::
        Term tyname name uni fun a
        -> InlineM tyname name uni fun a (Term tyname name uni fun a)
    handleTerm = \case
        v@(Var _ n) -> fromMaybe v <$> substName n
        Let a NonRec bs t -> do
            -- Process bindings, eliminating those which will be inlined unconditionally,
            -- and accumulating the new substitutions
            -- See Note [Removing inlined bindings]
            -- Note that we don't *remove* the bindings or scope the state, so the state will carry
            -- over into "sibling" terms. This is fine because we have global uniqueness
            -- (see Note [Inlining and global uniqueness]), if somewhat wasteful.
            bs' <- wither (processSingleBinding t) (toList bs)
            t' <- processTerm t
            -- Use 'mkLet': we're using lists of bindings rather than NonEmpty since we might
            -- actually have got rid of all of them!
            pure $ mkLet a NonRec bs' t'
        -- We cannot currently soundly do beta for types (see SCP-2570), so we just recognize
        -- immediately instantiated type abstractions here directly.
        (TyInst a (TyAbs a' tn k t) rhs) -> do
            b' <- maybeAddTySubst tn rhs
            t' <- processTerm t
            case b' of
                Just rhs' -> pure $ TyInst a (TyAbs a' tn k t') rhs'
                Nothing   -> pure t'
        -- This includes recursive let terms, we don't even consider inlining them at the moment
        t -> forMOf termSubterms t processTerm
    applyTypeSubstitution :: Type tyname uni a -> InlineM tyname name uni fun a (Type tyname uni a)
    applyTypeSubstitution t = gets isTypeSubstEmpty >>= \case
        -- The type substitution is very often empty, and there are lots of types in the program,
        -- so this saves a lot of work (determined from profiling)
        True -> pure t
        _    -> typeSubstTyNamesM substTyName t
    -- See Note [Renaming strategy]
    substTyName :: tyname -> InlineM tyname name uni fun a (Maybe (Type tyname uni a))
    substTyName tyname = gets (lookupType tyname) >>= traverse liftDupable
    -- See Note [Renaming strategy]
    substName :: name -> InlineM tyname name uni fun a (Maybe (Term tyname name uni fun a))
    substName name = gets (lookupTerm name) >>= traverse renameTerm
    -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
    renameTerm ::
        InlineTerm tyname name uni fun a
        -> InlineM tyname name uni fun a (Term tyname name uni fun a)
    renameTerm = \case
        -- Already processed term, just rename and put it in, don't do any
        -- further optimization here.
        Done t -> liftDupable t

{- Note [Renaming strategy]
Since we assume global uniqueness, we can take a slightly different approach to
renaming:  we rename the term we are substituting in, instead of renaming
every binder that our substitution encounters, which should guarantee that we
avoid any variable capture.

We rename both terms and types as both may have binders in them.
-}

-- | Run the inliner on a single non-recursive let binding.
processSingleBinding
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Term tyname name uni fun a -- ^ The body of the let binding.
    -> Binding tyname name uni fun a -- ^ The binding.
    -> InlineM tyname name uni fun a (Maybe (Binding tyname name uni fun a))
processSingleBinding body = \case
    TermBind a s v@(VarDecl _ n _) rhs -> do
        maybeRhs' <- maybeAddSubst body a s n rhs
        pure $ TermBind a s v <$> maybeRhs'
    TypeBind a v@(TyVarDecl _ n _) rhs -> do
        maybeRhs' <- maybeAddTySubst n rhs
        pure $ TypeBind a v <$> maybeRhs'
    -- Just process all the subterms
    b -> Just <$> forMOf bindingSubterms b processTerm

-- | Check against the heuristics we have for inlining and either inline the term binding or not.
-- The arguments to this function are the fields of the `TermBinding` being processed.
-- Nothing means that we are inlining the term:
--   * we have extended the substitution, and
--   * we are removing the binding (hence we return Nothing).
maybeAddSubst
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Term tyname name uni fun a
    -> a
    -> Strictness
    -> name
    -> Term tyname name uni fun a
    -> InlineM tyname name uni fun a (Maybe (Term tyname name uni fun a))
maybeAddSubst body a s n rhs = do
    rhs' <- processTerm rhs

    -- Check whether we've been told specifically to inline this
    hints <- view iiHints
    let hinted = shouldInline hints a n

    if hinted -- if we've been told specifically, then do it right away
    then extendAndDrop (Done $ dupable rhs')
    else do
        termIsPure <- checkPurity rhs'
        preUnconditional <- liftM2 (&&) (nameUsedAtMostOnce n) (effectSafe body s n termIsPure)
        -- similar to the paper, preUnconditional inlining checks that the binder is 'OnceSafe'.
        -- I.e., it's used at most once AND it neither duplicate code or work.
        -- While we don't check for lambda etc like in the paper, `effectSafe` ensures that it
        -- isn't doing any substantial work.
        -- We actually also inline 'Dead' binders (i.e., remove dead code) here.
        if preUnconditional
        then extendAndDrop (Done $ dupable rhs')
        else do
            -- See Note [Inlining approach and 'Secrets of the GHC Inliner'] and [Inlining and
            -- purity]. This is the case where we don't know that the number of occurrences is
            -- exactly one, so there's no point checking if the term is immediately evaluated.
            postUnconditional <- fmap ((&&) termIsPure) (acceptable rhs')
            if postUnconditional
            then extendAndDrop (Done $ dupable rhs')
            else pure $ Just rhs'
    where
        extendAndDrop ::
            forall b . InlineTerm tyname name uni fun a
            -> InlineM tyname name uni fun a (Maybe b)
        extendAndDrop t = modify' (extendTerm n t) >> pure Nothing

-- | Check if term is pure. See Note [Inlining and purity]
checkPurity
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    =>Term tyname name uni fun a -> InlineM tyname name uni fun a Bool
checkPurity t = do
    strctMap <- view iiStrictnessMap
    builtinVer <- view iiBuiltinVer
    let strictnessFun = \n' -> Map.findWithDefault NonStrict (n' ^. theUnique) strctMap
    pure $ isPure builtinVer strictnessFun t

nameUsedAtMostOnce :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => name
    -> InlineM tyname name uni fun a Bool
nameUsedAtMostOnce n = do
    usgs <- view iiUsages
    -- 'inlining' terms used 0 times is a cheap way to remove dead code while we're here
    pure $ Usages.getUsageCount n usgs <= 1

effectSafe :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Term tyname name uni fun a
    -> Strictness
    -> name
    -> Bool -- ^ is it pure?
    -> InlineM tyname name uni fun a Bool
effectSafe body s n purity = do
    -- This can in the worst case traverse a lot of the term, which could lead to us
    -- doing ~quadratic work as we process the program. However in practice most term
    -- types will make it give up, so it's not too bad.
    let immediatelyEvaluated = case firstEffectfulTerm body of
            Just (Var _ n') -> n == n'
            _               -> False
    pure $ case s of
        Strict    -> purity || immediatelyEvaluated
        NonStrict -> True

-- | Should we inline? Should only inline things that won't duplicate work or code.
-- See Note [Inlining approach and 'Secrets of the GHC Inliner']
acceptable ::  Term tyname name uni fun a -> InlineM tyname name uni fun a Bool
acceptable t =
    -- See Note [Inlining criteria]
    pure $ costIsAcceptable t && sizeIsAcceptable t

{- |
Try to identify the first sub term which will be evaluated in the given term and
which could have an effect. 'Nothing' indicates that we don't know, this function
is conservative.
-}
firstEffectfulTerm :: Term tyname name uni fun a -> Maybe (Term tyname name uni fun a)
firstEffectfulTerm = goTerm
    where
      goTerm = \case
        Let _ NonRec bs b -> case goBindings (NE.toList bs) of
            Just t' -> Just t'
            Nothing -> goTerm b

        Apply _ l _ -> goTerm l
        TyInst _ t _ -> goTerm t
        IWrap _ _ _ t -> goTerm t
        Unwrap _ t -> goTerm t

        t@Var{} -> Just t
        t@Error{} -> Just t
        t@Builtin{} -> Just t

        -- Hard to know what gets evaluated first in a recursive let-binding,
        -- just give up and say nothing
        (Let _ Rec _ _) -> Nothing
        TyAbs{} -> Nothing
        LamAbs{} -> Nothing
        Constant{} -> Nothing

      goBindings :: [Binding tyname name uni fun a] -> Maybe (Term tyname name uni fun a)
      goBindings [] = Nothing
      goBindings (b:bs) = case b of
        -- Only strict term bindings can cause effects
        TermBind _ Strict _ rhs -> goTerm rhs
        _                       -> goBindings bs

{- Note [Inlining criteria]
What gets inlined? Our goals are simple:
- Make the resulting program faster (or at least no slower)
- Make the resulting program smaller (or at least no bigger)
- Inline as much as we can, since it exposes optimization opportunities

There are two easy cases:
- Inlining approximately variable-sized and variable-costing terms (e.g. builtins, other variables)
- Inlining single-use terms

After that it gets more difficult. As soon as we're inlining things that are not variable-sized
and are used more than once, we are at risk of doing more work or making things bigger.

There are a few things we could do to do this in a more principled way, such as call-site inlining
based on whether a function is fully applied.
-}

{- Note [Inlining and purity]
When can we inline something that might have effects? We must remember that we often also
remove a binding that we inline.

For strict bindings, the answer is that we can't: we will delay the effects to the use site,
so they may happen multiple times (or none). So we can only inline bindings whose RHS is pure,
or if we can prove that the effects don't change. We take a conservative view on this,
saying that no effects change if:
- The variable is clearly the first possibly-effectful term evaluated in the body
- The variable is used exactly once (so we won't duplicate or remove effects)

For non-strict bindings, the effects already happened at the use site, so it's fine to inline it
unconditionally.
-}

-- | Check against the inlining heuristics for types and either inline it, returning Nothing, or
-- just return the type without inlining.
-- We only inline if (1) the type is used at most once OR (2) it's a `trivialType`.
maybeAddTySubst
    :: forall tyname name uni fun a . InliningConstraints tyname name uni fun
    => tyname -- ^ The type variable
    -> Type tyname uni a -- ^  The value of the type variable.
    -> InlineM tyname name uni fun a (Maybe (Type tyname uni a))
maybeAddTySubst tn rhs = do
    usgs <- view iiUsages
    -- No need for multiple phases here
    let typeUsedAtMostOnce = Usages.getUsageCount tn usgs <= 1
    if typeUsedAtMostOnce || trivialType rhs
    then do
        modify' (extendType tn rhs)
        pure Nothing
    else pure $ Just rhs

-- | Is the cost increase (in terms of evaluation work) of inlining a variable whose RHS is
-- the given term acceptable?
costIsAcceptable :: Term tyname name uni fun a -> Bool
costIsAcceptable = \case
  Builtin{}  -> True
  Var{}      -> True
  Constant{} -> True
  Error{}    -> True
  -- This will mean that we create closures at each use site instead of
  -- once, but that's a very low cost which we're okay rounding to 0.
  LamAbs{}   -> True
  TyAbs{}    -> True

  -- Arguably we could allow these two, but they're uncommon anyway
  IWrap{}    -> False
  Unwrap{}   -> False

  Apply{}    -> False
  TyInst{}   -> False
  Let{}      -> False

-- | Is the size increase (in the AST) of inlining a variable whose RHS is
-- the given term acceptable?
sizeIsAcceptable :: Term tyname name uni fun a -> Bool
sizeIsAcceptable = \case
  Builtin{}  -> True
  Var{}      -> True
  Error{}    -> True
  LamAbs {}  -> False
  TyAbs {}   -> False

  -- Arguably we could allow these two, but they're uncommon anyway
  IWrap{}    -> False
  Unwrap{}   -> False
  -- Constants can be big! We could check the size here and inline if they're
  -- small, but probably not worth it
  Constant{} -> False
  Apply{}    -> False
  TyInst{}   -> False
  Let{}      -> False

-- | Is this a an utterly trivial type which might as well be inlined?
trivialType :: Type tyname uni a -> Bool
trivialType = \case
    TyBuiltin{} -> True
    TyVar{}     -> True
    _           -> False
