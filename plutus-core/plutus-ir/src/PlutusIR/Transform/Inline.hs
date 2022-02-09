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
import PlutusIR.MkPir
import PlutusIR.Purity
import PlutusIR.Transform.Rename ()
import PlutusPrelude

import PlutusCore qualified as PLC
import PlutusCore.Builtin.Meaning qualified as PLC
import PlutusCore.InlineUtils
import PlutusCore.Name
import PlutusCore.Quote
import PlutusCore.Subst (typeSubstTyNamesM)

import Control.Lens hiding (Strict)
import Control.Monad.Reader
import Control.Monad.State

import Algebra.Graph qualified as G
import Data.Map qualified as Map
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Witherable

{- Note [Inlining approach and 'Secrets of the GHC Inliner']
The approach we take is more-or-less exactly taken from 'Secrets of the GHC Inliner'.

Overall, the cause of differences is that we are largely trying to just clean up some
basic issues, not do serious optimization. In many cases we've already run the GHC simplifier
on our input!

We differ from the paper a few ways, mostly leaving things out:

Functionality
------------

PreInlineUncoditional: we don't do it, since we don't bother using usage information.
We *could* do it, but it doesn't seem worth it. We also don't need to worry about
inlining nested let-bindings, since we don't inline any.

CallSiteInline: not worth it.

Inlining recursive bindings: not worth it, complicated.

Context-based inlining: we don't do CallSiteInline, so no point.

Beta reduction: not worth it, but would be easy. We could do the inlining of the argument
here and also detect dead immediately-applied-lambdas in the dead code pass.

Implementation
--------------

In-scope set: we don't bother keeping it, since we only ever substitute in things that
don't have bound variables. This is largely because we don't do PreInlineUnconditional, which
would inline big things that were only used once, including lambdas etc.

Suspended substitutions for values: we don't do it, since you only need it for
PreInlineUnconditional

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

-- 'SubstRng' in the paper, no 'Susp' case
-- See Note [Inlining approach and 'Secrets of the GHC Inliner']
newtype InlineTerm tyname name uni fun a = Done (Term tyname name uni fun a)

newtype TermEnv tyname name uni fun a = TermEnv { _unTermEnv :: UniqueMap TermUnique (InlineTerm tyname name uni fun a) }
    deriving newtype (Semigroup, Monoid)

newtype TypeEnv tyname uni a = TypeEnv { _unTypeEnv :: UniqueMap TypeUnique (Type tyname uni a) }
    deriving newtype (Semigroup, Monoid)

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
    , PLC.ToBuiltinMeaning uni fun
    , MonadQuote m
    )

type InliningConstraints tyname name uni fun =
    ( HasUnique name TermUnique
    , HasUnique tyname TypeUnique
    , PLC.ToBuiltinMeaning uni fun
    )


data InlineInfo name a = InlineInfo
    { _strictnessMap :: Deps.StrictnessMap
    , _usages        :: Usages.Usages
    , _hints         :: InlineHints name a
    }

-- Using a concrete monad makes a very large difference to the performance of this module (determined from profiling)
type InlineM tyname name uni fun a = ReaderT (InlineInfo name a) (StateT (Subst tyname name uni fun a) Quote)

lookupTerm
    :: (HasUnique name TermUnique)
    => name
    -> Subst tyname name uni fun a
    -> Maybe (InlineTerm tyname name uni fun a)
lookupTerm n subst = lookupName n $ subst ^. termEnv . unTermEnv

extendTerm
    :: (HasUnique name TermUnique)
    => name
    -> InlineTerm tyname name uni fun a
    -> Subst tyname name uni fun a
    -> Subst tyname name uni fun a
extendTerm n clos subst = subst & termEnv . unTermEnv %~ insertByName n clos

lookupType
    :: (HasUnique tyname TypeUnique)
    => tyname
    -> Subst tyname name uni fun a
    -> Maybe (Type tyname uni a)
lookupType tn subst = lookupName tn $ subst ^. typeEnv . unTypeEnv

isTypeSubstEmpty :: Subst tyname name uni fun a -> Bool
isTypeSubstEmpty (Subst _ (TypeEnv tyEnv)) = isEmpty tyEnv

extendType
    :: (HasUnique tyname TypeUnique)
    => tyname
    -> Type tyname uni a
    -> Subst tyname name uni fun a
    -> Subst tyname name uni fun a
extendType tn ty subst = subst &  typeEnv . unTypeEnv %~ insertByName tn ty

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
    -> Term tyname name uni fun a
    -> m (Term tyname name uni fun a)
inline hints t = let
        inlineInfo :: InlineInfo name a
        inlineInfo = InlineInfo (snd deps) usgs hints
        -- We actually just want the variable strictness information here!
        deps :: (G.Graph Deps.Node, Map.Map PLC.Unique Strictness)
        deps = Deps.runTermDeps t
        usgs :: Map.Map Unique Int
        usgs = Usages.runTermUsages t
    in liftQuote $ flip evalStateT mempty $ flip runReaderT inlineInfo $ processTerm t

{- Note [Removing inlined bindings]
We *do* remove bindings that we inline (since we only do unconditional inlining). We *could*
leave this to the dead code pass, but it's helpful to do it here.
Crucially, we have to do the same reasoning wrt strict bindings and purity (see Note [Inlining and purity]):
we can only inline *pure* strict bindings, which is effectively the same as what we do in the dead
code pass.

Annoyingly, this requires us to redo the analysis that we do for the dead binding pass.
TODO: merge them or figure out a way to share more work, especially since there's similar logic.
This might mean reinventing GHC's OccAnal...
-}

processTerm
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Term tyname name uni fun a
    -> InlineM tyname name uni fun a (Term tyname name uni fun a)
processTerm = handleTerm <=< traverseOf termSubtypes applyTypeSubstitution where
    handleTerm :: Term tyname name uni fun a -> InlineM tyname name uni fun a (Term tyname name uni fun a)
    handleTerm = \case
        v@(Var _ n) -> fromMaybe v <$> substName n
        Let a NonRec bs t -> do
            -- Process bindings, eliminating those which will be inlined unconditionally,
            -- and accumulating the new substitutions
            -- See Note [Removing inlined bindings]
            -- Note that we don't *remove* the bindings or scope the state, so the state will carry over
            -- into "sibling" terms. This is fine because we have global uniqueness
            -- (see Note [Inlining and global uniqueness]), if somewhat wasteful.
            bs' <- wither processSingleBinding (toList bs)
            t' <- processTerm t
            -- Use 'mkLet': we're using lists of bindings rather than NonEmpty since we might actually
            -- have got rid of all of them!
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
        -- The type substitution is very often empty, and there are lots of types in the program, so this saves a lot of work (determined from profiling)
        True -> pure t
        _    -> typeSubstTyNamesM substTyName t
    -- See Note [Renaming strategy]
    substTyName :: tyname -> InlineM tyname name uni fun a (Maybe (Type tyname uni a))
    substTyName tyname = gets (lookupType tyname) >>= traverse PLC.rename
    -- See Note [Renaming strategy]
    substName :: name -> InlineM tyname name uni fun a (Maybe (Term tyname name uni fun a))
    substName name = gets (lookupTerm name) >>= traverse renameTerm
    -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
    renameTerm :: InlineTerm tyname name uni fun a -> InlineM tyname name uni fun a (Term tyname name uni fun a)
    renameTerm = \case
        -- Already processed term, just rename and put it in, don't do any
        -- further optimization here.
        Done t -> PLC.rename t

{- Note [Renaming strategy]
Since we assume global uniqueness, we can take a slightly different approach to
renaming:  we rename the term we are substituting in, instead of renaming
every binder that our substitution encounters, which should guarantee that we
avoid any variable capture.

We rename both terms and types as both may have binders in them.
-}

processSingleBinding
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Binding tyname name uni fun a
    -> InlineM tyname name uni fun a (Maybe (Binding tyname name uni fun a))
processSingleBinding = \case
    TermBind a s v@(VarDecl _ n _) rhs -> do
        maybeRhs' <- maybeAddSubst a s n rhs
        pure $ TermBind a s v <$> maybeRhs'
    TypeBind a v@(TyVarDecl _ n _) rhs -> do
        maybeRhs' <- maybeAddTySubst n rhs
        pure $ TypeBind a v <$> maybeRhs'
    -- Just process all the subterms
    b -> Just <$> forMOf bindingSubterms b processTerm

-- NOTE:  Nothing means that we are inlining the term:
--   * we have extended the substitution, and
--   * we are removing the binding (hence we return Nothing)
maybeAddSubst
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => a
    -> Strictness
    -> name
    -> Term tyname name uni fun a
    -> InlineM tyname name uni fun a (Maybe (Term tyname name uni fun a))
maybeAddSubst a s n rhs = do
    rhs' <- processTerm rhs

    -- Check whether we've been told specifically to inline this
    hints <- asks _hints
    let hinted = shouldInline hints a n

    preUnconditional <- preInlineUnconditional rhs'
    if preUnconditional
    then extendAndDrop (Done rhs')
    else do
        -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
        postUnconditional <- postInlineUnconditional rhs'
        if hinted || postUnconditional
        then extendAndDrop (Done rhs')
        else pure $ Just rhs'
    where
        extendAndDrop :: forall b . InlineTerm tyname name uni fun a -> InlineM tyname name uni fun a (Maybe b)
        extendAndDrop t = modify' (extendTerm n t) >> pure Nothing

        checkPurity :: Term tyname name uni fun a -> InlineM tyname name uni fun a Bool
        checkPurity t = do
            strctMap <- asks _strictnessMap
            let strictnessFun = \n' -> Map.findWithDefault NonStrict (n' ^. theUnique) strctMap
            pure $ isPure strictnessFun t

        preInlineUnconditional :: Term tyname name uni fun a -> InlineM tyname name uni fun a Bool
        preInlineUnconditional t = do
            usgs <- asks _usages
            -- 'inlining' terms used 0 times is a cheap way to remove dead code while we're here
            let termUsedAtMostOnce = Usages.getUsageCount n usgs <= 1
            -- See Note [Inlining and purity]
            termIsPure <- checkPurity t
            pure $ termUsedAtMostOnce && case s of { Strict -> termIsPure; NonStrict -> True; }

        -- | Should we inline? Should only inline things that won't duplicate work or code.
        -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
        postInlineUnconditional ::  Term tyname name uni fun a -> InlineM tyname name uni fun a Bool
        postInlineUnconditional t = do
            -- See Note [Inlining criteria]
            let acceptable = costIsAcceptable t && sizeIsAcceptable t
            -- See Note [Inlining and purity]
            termIsPure <- checkPurity t
            pure $ acceptable && case s of { Strict -> termIsPure; NonStrict -> True; }

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
based on whether a funciton is fully applied.

For now, we have one special case that is a little questionable: inlining functions whose body is small
(motivating example: const). This *could* lead to code duplication, but it's a limited enough case that
we're just going to accept that risk for now. We'll need to be more careful if we inline more functions.

NOTE(MPJ): turns out this *does* lead to moderate size increases. We should fix this with some arity analysis
and context-sensitive inlining.
-}

{- Note [Inlining and purity]
When can we inline something that might have effects? We must remember that we often also
remove a binding that we inline.

For strict bindings, the answer is that we can't: we will delay the effects to the use site,
so they may happen multiple times (or none). So we can only inline bindings whose RHS is pure.

For non-strict bindings, the effects already happened at the use site, so it's fine to inline it
unconditionally.
-}

maybeAddTySubst
    :: forall tyname name uni fun a . InliningConstraints tyname name uni fun
    => tyname
    -> Type tyname uni a
    -> InlineM tyname name uni fun a (Maybe (Type tyname uni a))
maybeAddTySubst tn rhs = do
    usgs <- asks _usages
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
  Builtin{}      -> True
  Var{}          -> True
  Error{}        -> True
  -- See Note [Inlining criteria]
  LamAbs _ _ _ t -> sizeIsAcceptable t
  TyAbs _ _ _ t  -> sizeIsAcceptable t

  -- Arguably we could allow these two, but they're uncommon anyway
  IWrap{}        -> False
  Unwrap{}       -> False
  -- Constants can be big! We could check the size here and inline if they're
  -- small, but probably not worth it
  Constant{}     -> False
  Apply{}        -> False
  TyInst{}       -> False
  Let{}          -> False

-- | Is this a an utterly trivial type which might as well be inlined?
trivialType :: Type tyname uni a -> Bool
trivialType = \case
    TyBuiltin{} -> True
    TyVar{}     -> True
    _           -> False
