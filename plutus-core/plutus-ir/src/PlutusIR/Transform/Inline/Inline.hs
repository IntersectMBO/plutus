{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}

{- | An inlining pass of *non-recursive* bindings. It includes
(1) unconditional inlining: similar to `PreInlineUnconditionally` and `PostInlineUnconditionally`
in the paper 'Secrets of the GHC Inliner'.
(2) call site inlining of fully applied functions. See `Inline.CallSiteInline.hs`
-}

module PlutusIR.Transform.Inline.Inline (inline, InlineHints (..)) where
import PlutusIR
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.MkPir (mkLet)
import PlutusIR.Transform.Inline.Utils
import PlutusIR.Transform.Rename ()
import PlutusPrelude

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name
import PlutusCore.Quote
import PlutusCore.Rename (dupable)

import Control.Lens (forMOf, traverseOf)
import Control.Monad.Extra
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (evalStateT, modify')

import Algebra.Graph qualified as G
import Data.Map qualified as Map
import PlutusIR.Transform.Inline.CallSiteInline (inlineSaturatedApp)
import Witherable (Witherable (wither))

{- Note [Inlining approach and 'Secrets of the GHC Inliner']
The approach we take is more-or-less exactly taken from 'Secrets of the GHC Inliner'.

Overall, the cause of differences is that we are largely trying to just clean up some
basic issues, not do serious optimization. In many cases we've already run the GHC simplifier
on our input!

We differ from the paper a few ways, mostly leaving things out:

Functionality
------------

Inlining recursive bindings: not worth it, complicated.

Context-based inlining: Not needed atm.

Also, GHC implements many different optimization in a single simplifier pass.
The paper focusses on inlining, but does so in the context of GHC's monolithic simplifier, which
includes beta reduction and deadcode elimination.
We have opted to have more, single-purpose passes. See e.g. `Deadcode.hs` and `Beta.hs` for other
passes.

Implementation
--------------

In-scope set: we don't bother keeping it atm.

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

Unfortunately, we can't inline them even after we've compiled datatypes, because compiled datatypes
look like this (see Note [Abstract data types]). Here's an example with Maybe:

(/\Maybe :: * -> * .
  \Nothing :: forall a . Maybe a  .
  \Just :: forall a . a -> Maybe .
  \match_Maybe : forall r . Maybe a -> r -> (a -> r) -> r .
    <user term>
)
-- defn of Maybe
{ \ a . forall r . r -> (a -> r) -> r }
-- defn of Nothing
(/\ a . /\ r . \(nothing_case :: r) . \(just_case :: a -> r) . nothing_case)
-- defn of Just
(/\ a . \(x : a) . /\ r . \(nothing_case :: r) . \(just_case :: a -> r) . just_case x)
-- defn of match_Maybe
(/\ a . \(dt : forall r . r -> (a -> r) -> r) . dt)

The definitions of the constructors/destructor don't look like let-bindings because there
is a type abstraction in between the lambdas and their arguments! And this abstraction
is important: the bodies of the constructors/destructor only typecheck if they are
*outside* the type abstraction, because they fundamentally rely on knowing what the
type actually *is* in order to be able to construct/destruct it. e.g. for a Scott-encoded
type we actually need to know that the datatype is encoded as a matching function,
not just an abstract type. So we can't just put the definitions of the
constructors/destructor inside the type abstraction.

We *could* inline the datatype definition. That would get rid of the type abstraction,
letting us inline the constructors/destructor (by effectively making the datatype not
abstract inside the body). But this way lies madness: doing that consistently would
mean inlining the definitions of *all* datatypes, which would enormously (exponentially!)
bloat the types inside, making the typechecker (and everything else that processes the
AST) incredibly slow.

So it seems that we're stuck. We can't inline destructors in PIR.

But we *can* do it in UPLC! No types, so no problem. The type abstraction/instantiation will
turn into a delay/force pair and get simplified away, and then we have something that we can
inline. This is essentially the reason for the existence of the UPLC inlining pass.

Note that much the same reasoning applies to constructors also. The main difference
is that they might not be applied saturated, so it's not _always_ clear that we want to
inline them. But at least in UPLC we _can_ inline them.
-}

{- Note [Inlining and global uniqueness]
Inlining relies on global uniqueness for two reasons:
1. We track various things in big maps keyed by unique. This is tricky without global
uniqueness, but very straightforward with it: since names are globally unique, we can
just use them as map keys and not worry about things.
2. You need global uniqueness to be able to do substitution without worrying about
avoiding variable capture.

Inlining things can break global uniqueness, because it can duplicate terms, and those
terms can have binders in them.

There are two ways to approach this:
1. Try to maintain global uniqueness
2. Carefully track which terms have been potentially duplicated, and make sure you never
do anything unsafe with them.

We could probably do 2, but it is tricky and requires subtle argumentation to establish
its safety.  On the other hand, it is actually very easy to do 1: just rename terms
when we substitute them in! This is much more obviously correct since it maintains the
global uniqueness invariant. The only cost is that we won't have any pre-computed
information about the fresh variables (e.g. usage counts), since we compute all that
up-front. But this can only bit us if we process the renamed terms (which we currently
don't), and the effect would only be slightly worse optimization.

Renaming everything is a bit overkill, it corresponds to 'The sledgehammer' in 'Secrets'.
But we don't really care about the costs listed there: it's easy for us to get a name
supply, and the performance cost does not currently seem relevant. So it's fine.
-}

-- | Inline non-recursive bindings. Relies on global uniqueness, and preserves it.
-- See Note [Inlining and global uniqueness]
inline
    :: forall tyname name uni fun ann m
    . ExternalConstraints tyname name uni fun m
    => InlineHints name ann
    -> PLC.BuiltinSemanticsVariant fun
    -> Term tyname name uni fun ann
    -> m (Term tyname name uni fun ann)
inline hints semvar t = let
        inlineInfo :: InlineInfo name fun ann
        inlineInfo = InlineInfo (snd deps) usgs hints semvar
        -- We actually just want the variable strictness information here!
        deps :: (G.Graph Deps.Node, Map.Map PLC.Unique Strictness)
        deps = Deps.runTermDeps semvar t
        usgs :: Usages.Usages
        usgs = Usages.termUsages t
    in liftQuote $ flip evalStateT mempty $ flip runReaderT inlineInfo $ processTerm t

{- Note [Removing inlined bindings]
We *do* remove bindings that we inline *unconditionally*. We *could*
leave this to the dead code pass, but it's helpful to do it here.
We *don't* remove bindings that we inline at the call site.
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
    :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Term tyname name uni fun ann -- ^ Term to be processed.
    -> InlineM tyname name uni fun ann (Term tyname name uni fun ann)
processTerm = handleTerm <=< traverseOf termSubtypes applyTypeSubstitution where
    handleTerm ::
        Term tyname name uni fun ann
        -> InlineM tyname name uni fun ann (Term tyname name uni fun ann)
    handleTerm = \case
        v@(Var _ n) -> fromMaybe v <$> substName n
        Let ann NonRec bs t -> do
            -- Process bindings, eliminating those which will be inlined unconditionally,
            -- and accumulating the new substitutions.
            -- See Note [Removing inlined bindings]
            -- Note that we don't *remove* the bindings or scope the state, so the state will carry
            -- over into "sibling" terms. This is fine because we have global uniqueness
            -- (see Note [Inlining and global uniqueness]), if somewhat wasteful.
            bs' <- wither (processSingleBinding t) (toList bs)
            t' <- processTerm t
            -- Use 'mkLet': we're using lists of bindings rather than NonEmpty since we might
            -- actually have got rid of all of them!
            pure $ mkLet ann NonRec bs' t'
        -- This includes recursive let terms, we don't even consider inlining them at the moment
        t ->
            -- process all subterms first, so that the rhs won't be processed more than once. This
            -- is important because otherwise the number of times we process them can grow
            -- exponentially in the case that it has nested `let`s.
            --
            -- Then, consider call site inlining for each node that have gone through unconditional
            -- inlining. Because `inlineSaturatedApp` traverses *all* application nodes for each
            -- subterm, the runtime is quadratic for terms with a long chain of applications.
            -- If we use the context-based approach like in GHC, this won't be a problem, so we may
            -- consider that in the future.
            inlineSaturatedApp =<< forMOf termSubterms t processTerm

-- | Run the inliner on a single non-recursive let binding.
processSingleBinding
    :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Term tyname name uni fun ann -- ^ The body of the let binding.
    -> Binding tyname name uni fun ann -- ^ The binding.
    -> InlineM tyname name uni fun ann (Maybe (Binding tyname name uni fun ann))
processSingleBinding body = \case
    (TermBind ann s v@(VarDecl _ n _) rhs0) -> do
        -- we want to do unconditional inline if possible
        maybeAddSubst body ann s n rhs0 >>= \case
            -- this binding is going to be unconditionally inlined
            Nothing -> pure Nothing
            Just rhs -> do
                -- when we encounter a binding, we add it to
                -- the global map `Utils.NonRecInScopeSet`.
                -- The `varRhs` added to the map has been unconditionally inlined.
                -- When we check the body of the let binding we look in this map for
                -- call site inlining.
                -- We don't remove the binding because we decide *at the call site*
                -- whether we want to inline, and it may be called more than once.
                modify' $
                    extendVarInfo
                        n
                        (MkVarInfo s (Done (dupable rhs)))
                pure $ Just $ TermBind ann s v rhs
    (TypeBind ann v@(TyVarDecl _ n _) rhs) -> do
        maybeRhs' <- maybeAddTySubst n rhs
        pure $ TypeBind ann v <$> maybeRhs'
    b -> -- Just process all the subterms
        Just <$> forMOf bindingSubterms b processTerm

-- | Check against the heuristics we have for inlining and either inline the term binding or not.
-- The arguments to this function are the fields of the `TermBinding` being processed.
-- Nothing means that we are inlining the term:
--   * we have extended the substitution, and
--   * we are removing the binding (hence we return Nothing).
maybeAddSubst
    :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Term tyname name uni fun ann
    -> ann
    -> Strictness
    -> name
    -> Term tyname name uni fun ann
    -> InlineM tyname name uni fun ann (Maybe (Term tyname name uni fun ann))
maybeAddSubst body ann s n rhs0 = do
    rhs <- processTerm rhs0

    -- Check whether we've been told specifically to inline this
    hints <- view iiHints
    let hinted = shouldInline hints ann n

    if hinted -- if we've been told specifically, then do it right away
    then extendAndDrop (Done $ dupable rhs)
    else
        ifM
            (shouldUnconditionallyInline s n rhs body)
            (extendAndDrop (Done $ dupable rhs))
            (pure $ Just rhs)
    where
        extendAndDrop ::
            forall b . InlineTerm tyname name uni fun ann
            -> InlineM tyname name uni fun ann (Maybe b)
        extendAndDrop t = modify' (extendTerm n t) >> pure Nothing

-- | Check against the inlining heuristics for types and either inline it, returning Nothing, or
-- just return the type without inlining.
-- We only inline if (1) the type is used at most once OR (2) it's a `trivialType`.
maybeAddTySubst
    :: forall tyname name uni fun ann . InliningConstraints tyname name uni fun
    => tyname -- ^ The type variable
    -> Type tyname uni ann -- ^  The value of the type variable.
    -> InlineM tyname name uni fun ann (Maybe (Type tyname uni ann))
maybeAddTySubst tn rhs = do
    usgs <- view iiUsages
    -- No need for multiple phases here
    let typeUsedAtMostOnce = Usages.getUsageCount tn usgs <= 1
    if typeUsedAtMostOnce || trivialType rhs
    then do
        modify' (extendType tn rhs)
        pure Nothing
    else pure $ Just rhs
