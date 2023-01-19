{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}

{-|
Call site inlining machinery. For now there's only one part: inlining of fully applied functions.
See ADR TODO for motivation. We inline fully applied functions if the cost and size are acceptable.
See note [Inlining of fully applied functions].
-}

module PlutusIR.Transform.Inline.CallSiteInline (callSiteInline) where

import Algebra.Graph qualified as G
import Control.Lens hiding (Strict)
import Control.Monad.Reader
import Control.Monad.State
import Data.Map qualified as Map
import PlutusCore.Builtin qualified as PLC
import PlutusCore.InlineUtils
import PlutusCore.Name qualified as PLC
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusCore.Subst
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.Core
import PlutusIR.MkPir
import PlutusIR.Transform.Inline.Utils
import PlutusIR.Transform.Rename ()
import PlutusPrelude
import Witherable (Witherable (wither))

{- Note [Inlining of fully applied functions]

We inline if (1) a function is fully applied (2) if its cost and size are acceptable. We discuss
each in detail below.

(1) What do we mean by "fully applied"?

Consider `let v = rhs in body`, in which `body` calls `v`.

We consider cases when `v` is a function/lambda abstraction(s). I.e.:

let v = \x1.\x2...\xn.VBody in body

In the `body`, where `v` is *called*,
if it was given `n` arguments, then it is _fully applied_ in the `body`.
We inline the call of the fully applied `v` in this case, i.e.,
we replace `v` in the `body` with `rhs`. E.g.

let f = \x.\y -> x
in
  let z = f q
  in f a b

becomes

let f = \x.\y -> x
in
  let z = f q
  in ((\x.\y -> x) a b)

With beta reduction, it becomes:

let f = \x.\y -> x
in
  let z = f q
  in a (more accurately it becomes (let { x = a, y = b } in x))

This is already a reduction in code size. However, because of this,
our dead code elimination pass is able to further reduce the code to just `a`. Consider

let f = \x.\y -> x
    z = f q
in f a b + z c

Here we have a `f` that is fully applied (`f a b`), and so we inline it:

let f = \x.\y -> x
in
  let z = f q
  in a + z c

We cannot eliminate the let-binding of `f` because it is not dead (it's called in `z`).
We don't inline `z` because it's not a lambda abstraction, it's an application.

To find out whether a function is fully applied,
we first need to count the number of type/term lambda abstractions,
so we know how many term/type arguments they have.

We pattern match the _rhs_ with `LamAbs` and `TyAbs` (lambda abstraction for terms or types),
and track the sequence of lambdas.
Then, in the _body_, we track the term and type application (`Apply` or `TyInst`) of _v_.

If _v_ is fully applied in the body, i.e., if the sequence of type and term lambda abstractions is
exactly matched by the corresponding sequence of type and term applications, then
we inline _v_, i.e., replace its occurrence with _rhs_ in the _body_. Because PIR is typed,
over-application of a function should not occur, so we don't need to worry about that.

Because a function can be called in the `body` multiple times and may not be fully applied for all
its calls, we cannot simply keep a simple substitution map like in `UnconditionalInline`,
which substitute *all* occurrences of a variable. Also, because we are inlining lambda abstractions,
we need to keep track of the in-scope set. See note [Inlining a lambda abstraction].

Below are some more examples:

Example 1: function in body

let f = \x . x
in let g = \y . f
   in g a

`f` and `g` each has 1 lambda. However, `g`'s _body_ includes `f` which also has a lambda.
Since we only count the number of lambdas, `g` is fully applied, and we inline.
`g a` reduces to `f`, which reduces the amount of code. Again, this also opens up more dead code
elimination opportunities.

Example 2: function as an argument

let id :: forall a . a -> a
    id x = x
in id {int -> int} (\x -> x +1)

Here we have a type application for a function that takes one type variable.
I.e., it's fully applied in terms of type.
In terms of terms, `id` takes one argument, and is indeed applied to one.
So `id` is fully applied! And we inline it.
Inlining and reducing `id` reduces the amount of code, as desired.

Example 3: function application in _rhs_

let f = (\x.\y.x+y) 4
in f 5

With beta-reduction, `f` becomes `\y.4+y` and it has 1 lambda.
The _body_ `f 5` is a fully applied function!
We can reduce it to 4+5.

Example 4: applications and lambda abstractions in _body_

let f = \x.\y.x+y
in (\z.f 3 4) 2

With beta-reduction, the _body_ becomes `f 3 4` and thus `f` is fully applied.

(2) How do we decide whether cost and size are acceptable?

We currently reuse the heuristics 'Utils.sizeIsAcceptable' and 'Utils.costIsAcceptable'
that are used in 'UnconditionalInline'. For

let v = \x1.\x2...\xn.VBody in body

we check `VBody` with the above "acceptable" functions.
Note that all `LamAbs` and `TyAbs` should have been
counted out already so we should not immediately encounter those in `VBody`.
Also, we currently reject `Constant` (has acceptable cost but not acceptable size).
We may want to check their sizes instead of just rejecting them.
-}

-- | Inline fully applied functions. Note [Inlining of fully applied functions].
-- Preserves global uniqueness. See Note [Inlining a lambda abstraction].
callSiteInline
    :: forall tyname name uni fun a m
    . ExternalConstraints tyname name uni fun m
    => InlineHints name a
    -> PLC.BuiltinVersion fun
    -> Term tyname name uni fun a
    -> m (Term tyname name uni fun a)
callSiteInline hints ver t = let
        inlineInfo :: InlineInfo name fun a
        inlineInfo = InlineInfo (snd deps) usgs hints ver
        -- We actually just want the variable strictness information here!
        deps :: (G.Graph Deps.Node, Map.Map PLC.Unique Strictness)
        deps = Deps.runTermDeps ver t
        usgs :: Usages.Usages
        usgs = Usages.termUsages t
    in liftQuote $ flip evalStateT mempty $ flip runReaderT inlineInfo $ processTerm t

{- Note [Removing inlined bindings]
We *do not* remove bindings that we inline here, we leave this to the dead code pass.
TODO
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
        -- See section 7.1 of the paper.
        -- When we encounter a variable, look it up in the substitution.
        v@(Var _ n) -> do
          substitution <- substName n
          case substitution of
            -- if it's not in the substitution, consider inlining it.
            Nothing  -> considerInline v
            -- otherwise, inline it.
            Just sub -> pure sub
        Let a NonRec bs t -> do
            -- Process bindings, checking for fully applied functions and
            -- put them in the substitution.
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
    -- Already processed term, just rename and put it in, don't do any further optimization here.
    renameTerm ::
        InlineTerm tyname name uni fun a
        -> InlineM tyname name uni fun a (Term tyname name uni fun a)
    renameTerm (Done t) = liftDupable t
    -- | See note [Inlining of fully applied functions].
    -- Consider inlining the variable that is NOT in the substitution by checking
    -- (1) Is it fully applied?
    -- (2) Are the cost and size acceptable?
    considerInline ::
        Term tyname name uni fun a
        -> InlineM tyname name uni fun a (Term tyname name uni fun a)
    considerInline v@(Var _ n) = undefined
    -- look up the variable in the `CalledVar` map
    -- if it's not in there or its `LamOrder` is an empty list, don't inline.
    -- if fullyApplied && acceptable then inline else
    considerInline notVar =
      Prelude.error "considerInline: should be a variable."

-- | Run the inliner on a single non-recursive let binding.
processSingleBinding
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Term tyname name uni fun a -- ^ The body of the let binding.
    -> Binding tyname name uni fun a -- ^ The binding.
    -> InlineM tyname name uni fun a (Maybe (Binding tyname name uni fun a))
processSingleBinding body = \case
    -- when the let binding is a function type,
    -- we consider whether we want to inline at the call site.
    TermBind a s v@(VarDecl _ n (TyFun _ tyArg tyBody)) rhs -> do
        let lamOrder = countLam rhs --TODO
        pure Nothing
    -- For anything else, just process all the subterms
    b -> Just <$> forMOf bindingSubterms b processTerm

-- | For keeping track of term lambda or type lambda of a let-binding.
data LamKind = TermLam | TypeLam deriving stock (Eq)

-- | A list of `LamAbs` and `TyAbs`, in order, of a let-binding.
type LamOrder = [LamKind]

-- | A mapping of a let-binding to its unique name and its definition and `LamOrder`.
newtype CalledVar tyname name uni fun a =
    MkCalledVar (PLC.UniqueMap PLC.TermUnique (CalledVarInfo tyname name uni fun a))
    deriving newtype (Semigroup, Monoid)

-- | Info attached to a let-binding needed for call site inlining.
data CalledVarInfo tyname name uni fun a =
  MkCalledVarInfo {
    def        :: Term tyname name uni fun a -- ^ its definition
    , lamOrder :: LamOrder -- ^ its sequence of term and type lambdas
  }

-- | Counts the number of type and term lambdas in the RHS of a binding and returns an ordered list
countLam ::
    Term tyname name uni fun a -- ^ the RHS of the let binding
    -> LamOrder
countLam = countLamInner []
    where
      countLamInner ::
        LamOrder
        -> Term tyname name uni fun a -- ^ The rhs term that is being counted.
        -> LamOrder
      countLamInner currLamOrder (LamAbs _a _n _ty body) =
        -- If the term is a term lambda abstraction, add it to the list, and
        -- keep on examining the body.
        countLamInner (currLamOrder <> [TermLam]) body
      countLamInner currLamOrder (TyAbs _a _n _kind body) =
        -- If the term is a type lambda abstraction, add it to the list, and
        -- keep on examining the body.
        countLamInner (currLamOrder <> [TypeLam]) body
      countLamInner currLamOrder _ =
        -- Whenever we encounter a body that is not a lambda abstraction, we are done counting
        currLamOrder

-- findLetVar

-- | Count the number of type and term applications in the body and return an ordered list of
-- applied `LamKind` and its corresponding let variable, if any.
countApp ::
    Term tyname name uni fun a -- ^ the body
    -> (Maybe name, LamOrder)
countApp = countAppInner []
    where
      countAppInner ::
        LamOrder
        -> Term tyname name uni fun a -- ^ The rhs term that is being counted.
        -> (Maybe name, LamOrder)
      countAppInner currLamOrder (Apply _ _ body) =
        -- If the term is a term application, add it to the list, and
        -- keep on examining the body.
        countAppInner (currLamOrder <> [TermLam]) body
      countAppInner currLamOrder (TyInst _ body _) =
        -- If the term is a type application, add it to the list, and
        -- keep on examining the body.
        countAppInner (currLamOrder <> [TypeLam]) body
      countAppInner currLamOrder (Var _ name) =
        -- When we encounter a body that is a variable, we are done counting applications.
        -- Return the variable (function) name along with its applied lambdas.
        (Just name, currLamOrder)
      countAppInner currLamOrder tm =
        -- TODO need to figure out example 4 in note [Inlining of fully applied functions]
        -- lam and app can cancel out with beta-reduction until we get to the variable
        (Nothing, countLam tm)


{- Note [Inlining a lambda abstraction]

Because a function can be called in the `body` multiple times and may not be fully applied for all
its calls, we cannot simply keep a simple substitution map like in `UnconditionalInline`,
which substitute *all* occurrences of a variable.

Also, because we are inlining lambda abstractions, to preserve uniqueness,
we follow section 3.2 ("The rapier") of the paper:

Our substitution algorithm has three parameters:
1. the expression to which the substitution is applied,
2. the substitution itself, and
3. the set of in-scope variables

Consider let x = E in B

We retain the let binding, adds x to the in-scope set. While processing B,
at *every* occurrence of x, we consider whether to inline it.

If x is not already in scope, the substitution is not changed, but the in-scope set is
extended by binding x to E'. If x is already in scope, then a new variable
name x' is invented (by getting a fresh unique); the substitution is extended by binding
x to DoneEx x', and the in-scope set is extended by binding x' to E'.



The DEFAULT alternative matches any constructors other
than Red, Blue, and Green. GHC supports such DEFAULT
alternatives directly, rather than requiring case expressions
to be exhaustive, which is dreadful for large data types. In-
side E, what is known about x? What we know is that it
is not bound to Red, Blue, or Green. This can be useful;
if E contains a case expression that scrutinises x, we can
4 The expression E1 `seq` E2 evaluates E1, discards the result, and
then evaluates and returns E2.
13replace x by x1! The right thing to do is to continue with
the empty substitution.
The code is simple enough, but it took us a long time before
the interplay between the substitution and the in-scope set
became as simple and elegant as it now is.

Suppose we write the call subst M [E=x] to mean the result of substituting E for x in M.
The standard rule for substitution when M is a lambda abstraction is:
subst (\x:M ) [E=x] = \x:M
subst (\x:M ) [E=y ] = \x:(subst M [E=y ])
if x does not occur free in E
-}
