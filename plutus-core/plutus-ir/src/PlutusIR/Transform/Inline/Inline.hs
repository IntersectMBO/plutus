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
import PlutusCore.Rename (dupable, liftDupable)
import PlutusCore.Subst (typeSubstTyNamesM)

import Control.Lens hiding (Strict)
import Control.Monad.Reader
import Control.Monad.State

import Algebra.Graph qualified as G
import Data.Map qualified as Map
import PlutusIR.Transform.Inline.CallSiteInline (computeArity, considerInlineSat)
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
Inlining relies on global uniqueness (we store things in a unique map), and *does* currently
preserve it because we don't inline anything with binders in unconditional inlining.

With call site inlining, we do inlining things with binders in them. We will give the binders fresh
name when we substitute in to preserve uniqueness in that case. TODO in a follow up PR.
-}

-- | Inline non-recursive bindings. Relies on global uniqueness, and preserves it.
-- See Note [Inlining and global uniqueness]
inline
    :: forall tyname name uni fun ann m
    . ExternalConstraints tyname name uni fun m
    => InlineHints name ann
    -> PLC.BuiltinVersion fun
    -> Term tyname name uni fun ann
    -> m (Term tyname name uni fun ann)
inline hints ver t = let
        inlineInfo :: InlineInfo name fun ann
        inlineInfo = InlineInfo (snd deps) usgs hints ver
        -- We actually just want the variable strictness information here!
        deps :: (G.Graph Deps.Node, Map.Map PLC.Unique Strictness)
        deps = Deps.runTermDeps ver t
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
        t -> do
            -- process all subterms first, so that the rhs won't be processed more than once. This
            -- is important because otherwise the number of times we process them can grow
            -- exponentially in the case that it has nested `let`s.
            processedT <- forMOf termSubterms t processTerm
            -- consider call site inlining for each node that have gone through unconditional
            -- inlining. Because `considerInlineSat` traverses *all* application nodes for each
            -- subterm, the runtime is quadratic for terms with a long chain of applications.
            -- If we use the context-based approach like in GHC, this won't be a problem, so we may
            -- consider that in the future.
            considerInlineSat processedT

applyTypeSubstitution :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Type tyname uni ann
    -> InlineM tyname name uni fun ann (Type tyname uni ann)
applyTypeSubstitution t = gets isTypeSubstEmpty >>= \case
    -- The type substitution is very often empty, and there are lots of types in the program,
    -- so this saves a lot of work (determined from profiling)
    True -> pure t
    _    -> typeSubstTyNamesM substTyName t

-- See Note [Renaming strategy]
substTyName :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => tyname
    -> InlineM tyname name uni fun ann (Maybe (Type tyname uni ann))
substTyName tyname = gets (lookupType tyname) >>= traverse liftDupable

-- See Note [Renaming strategy]
substName :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => name
    -> InlineM tyname name uni fun ann (Maybe (Term tyname name uni fun ann))
substName name = gets (lookupTerm name) >>= traverse renameTerm

-- See Note [Inlining approach and 'Secrets of the GHC Inliner']
-- Already processed term, just rename and put it in, don't do any further optimization here.
renameTerm :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => InlineTerm tyname name uni fun ann
    -> InlineM tyname name uni fun ann (Term tyname name uni fun ann)
renameTerm (Done t) = liftDupable t

{- Note [Renaming strategy]
Since we assume global uniqueness, we can take a slightly different approach to
renaming:  we rename the term we are substituting in, instead of renaming
every binder that our substitution encounters, which should guarantee that we
avoid any variable capture.

We rename both terms and types as both may have binders in them.
-}

-- | Run the inliner on a single non-recursive let binding.
processSingleBinding
    :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Term tyname name uni fun ann -- ^ The body of the let binding.
    -> Binding tyname name uni fun ann -- ^ The binding.
    -> InlineM tyname name uni fun ann (Maybe (Binding tyname name uni fun ann))
processSingleBinding body = \case
    (TermBind ann s v@(VarDecl _ n _) rhs) -> do
        -- we want to do unconditional inline if possible
        maybeRhs' <- maybeAddSubst body ann s n rhs
        case maybeRhs' of
            -- this binding is going to be unconditionally inlined
            Nothing -> pure Nothing
            Just processedRhs -> do
                let (varArity, bodyToCheck) = computeArity rhs
                -- when we encounter a binding, we add it to
                -- the global map `Utils.NonRecInScopeSet`.
                -- The `varDef` added to the map has been unconditionally inlined.
                -- When we check the body of the let binding we look in this map for
                -- call site inlining.
                -- We don't remove the binding because we decide *at the call site*
                -- whether we want to inline, and it may be called more than once.
                void $ modify' $ extendVarInfo n (MkVarInfo s processedRhs varArity bodyToCheck)
                pure $ Just $ TermBind ann s v processedRhs
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
maybeAddSubst body ann s n rhs = do
    rhs' <- processTerm rhs

    -- Check whether we've been told specifically to inline this
    hints <- view iiHints
    let hinted = shouldInline hints ann n

    if hinted -- if we've been told specifically, then do it right away
    then extendAndDrop (Done $ dupable rhs')
    else do
        isTermPure <- checkPurity rhs'
        preUnconditional <- liftM2 (&&) (nameUsedAtMostOnce n) (effectSafe body s n isTermPure)
        -- similar to the paper, preUnconditional inlining checks that the binder is 'OnceSafe'.
        -- I.e., it's used at most once AND it neither duplicate code or work.
        -- While we don't check for lambda etc like in the paper, `effectSafe` ensures that it
        -- isn't doing any substantial work.
        -- We actually also inline 'Dead' binders (i.e., remove dead code) here.
        if preUnconditional
        then extendAndDrop (Done $ dupable rhs')
        else do
            isBindingPure <- isTermBindingPure s rhs'
            -- See Note [Inlining approach and 'Secrets of the GHC Inliner'] and [Inlining and
            -- purity]. This is the case where we don't know that the number of occurrences is
            -- exactly one, so there's no point checking if the term is immediately evaluated.
            let postUnconditional = isBindingPure && sizeIsAcceptable rhs' && costIsAcceptable rhs'
            if postUnconditional
            then extendAndDrop (Done $ dupable rhs')
            else pure $ Just rhs'
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
