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
import Annotation
import Control.Lens hiding (Strict)
import Control.Monad.Reader
import Control.Monad.State
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusCore.Quote
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.Core
import PlutusIR.Transform.Inline.Utils
import PlutusPrelude

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
over-application of a function should not occur, so we don't need to worry about that. See note
[Identifying fully applied call sites].

Because a function can be called in the `body` multiple times and may not be fully applied for all
its calls, we cannot simply keep a simple substitution map like in `UnconditionalInline`,
which substitute *all* occurrences of a variable.

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
callSiteInline
    :: forall tyname name uni fun a m
    . (ExternalConstraints tyname name uni fun m, Eq a, Ord name)
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

-- | Run the inliner on a `Core.Type.Term`.
processTerm
    :: forall tyname name uni fun a. (InliningConstraints tyname name uni fun, Eq a, Ord name)
    => Term tyname name uni fun a -- ^ Term to be processed.
    -> InlineM tyname name uni fun a (Term tyname name uni fun a)
processTerm = \case
    -- When we encounter a variable, consider inlining it.
    v@(Var _a _n) -> do
      considerInline v
    Let a NonRec bs t -> do
        -- Process non-recursive let bindings, checking for fully applied functions and
        -- put them in the substitution. We do NOT remove the inlined binding here because it
        -- may not be dead. We leave this to the dead code pass.
        bs' <- traverse (processSingleBinding t) bs
        t' <- processTerm t
        pure $ Let a NonRec bs' t' -- we're not removing any bindings so it should be nonempty!
    -- TODO Let a Rec bs t -> do
      -- Process recursive let bindings, looking for let-bindings that are functions and are
      -- recursively called.
    t -> forMOf termSubterms t processTerm
    -- | See note [Inlining of fully applied functions].
    -- Consider inlining the variable that is NOT in the substitution by checking
    -- (1) Is it fully applied?
    -- (2) Are the cost and size acceptable?
    where
    considerInline ::
        Term tyname name uni fun a -- the variable that is a function
        -> InlineM tyname name uni fun a (Term tyname name uni fun a)
    considerInline v@(Var a n) = do
      -- look up the variable in the `CalledVar` map
      varInfo <- gets (lookupCalled n)
      case varInfo of
        -- if it's not in the map, it's not a function, don't inline.
        Nothing -> pure v
        Just info -> do
          let subst = calledVarDef info -- what we substitute in is its definition
          isAcceptable <- acceptable subst
          -- if the size and cost are not acceptable, don't inline
          if not isAcceptable then pure v
          else do -- if the size and cost are acceptable, then check if it's fully applied
            -- it's fully applied if its annotation (`a`) is in the list of fully applied called
            -- locations
            pure $ if a `elem` calledLocation info then subst else v
    considerInline _notVar = -- this should not happen
      Prelude.error  "considerInline: should be a variable."

-- | Run the inliner on a single non-recursive let binding.
processSingleBinding
    :: forall tyname name uni fun a. (InliningConstraints tyname name uni fun, Eq a, Ord name)
    => Term tyname name uni fun a -- ^ The body of the let binding.
    -> Binding tyname name uni fun a -- ^ The binding.
    -> InlineM tyname name uni fun a (Binding tyname name uni fun a)
processSingleBinding body = \case
    -- when the let binding is a function type, we add it to the `CalledVarEnv` and
    -- consider whether we want to inline at the call site.
    TermBind a s v@(VarDecl _ n (TyFun _ _tyArg _tyBody)) rhs -> do
        let
          -- track the term and type lambda abstraction order of the function
          varLamOrder = countLam rhs
          -- examine the `body` of the `Let` term and track all term/type applications
          appSites = countApp body
          -- list of all call sites of this variable
          listOfCallSites = Map.lookup n appSites
        case listOfCallSites of
          Nothing ->
            -- we don't remove the binding because we decide *at the call site* whether we want to
            -- inline, and it may be called more than once
            pure $ TermBind a s v rhs
          Just list -> do
            let
              isEqAppOrder :: ApplicationOrder a -> Bool
              isEqAppOrder appOrder = applicationOrder appOrder == varLamOrder
              -- filter the list to only call locations that are fully applied
              filteredFullyApplied = filter isEqAppOrder list
              fullyAppliedAnns = fmap annotation filteredFullyApplied
            -- add the function to `CalledVarEnv`
            void $ modify' $ extendCalled n (MkCalledVarInfo rhs varLamOrder fullyAppliedAnns)
            pure $ TermBind a s v rhs
    -- when the let binding is a type lambda abstraction, we add it to the `CalledVarEnv` and
    -- consider whether we want to inline at the call site.
    TermBind a s v@(VarDecl _ n (TyLam _ann _tyname _tyArg _tyBody)) rhs -> do
        let varLamOrder = countLam rhs
            appSites = countApp body
            listOfCallSites = Map.lookup n appSites
        case listOfCallSites of
            Nothing ->
              -- we don't remove the binding because we decide *at the call site* whether we want to
              -- inline, and it may be called more than once
              pure $ TermBind a s v rhs
            Just list -> do
              let
                isEqAppOrder :: ApplicationOrder a -> Bool
                isEqAppOrder appOrder = applicationOrder appOrder == varLamOrder
                -- filter the list to only call locations that are fully applied
                filteredFullyApplied = filter isEqAppOrder list
                fullyAppliedAnns = fmap annotation filteredFullyApplied
              -- add the function to `CalledVarEnv`
              -- add the type abstraction to `CalledVarEnv`
              void $ modify' $ extendCalled n (MkCalledVarInfo rhs varLamOrder fullyAppliedAnns)
              -- we don't remove the binding because we decide *at the call site* whether we want to
              -- inline, and it may be called more than once
              pure $ TermBind a s v rhs
    -- For anything else, just process all the subterms
    b -> forMOf bindingSubterms b processTerm

-- | Counts the type and term lambdas in the RHS of a binding and returns an ordered list
countLam ::
    Term tyname name uni fun a -- ^ the RHS of the let binding
    -> TermOrTypeOrder
countLam = countLamInner []
    where
      countLamInner ::
        TermOrTypeOrder
        -> Term tyname name uni fun a -- ^ The rhs term that is being counted.
        -> TermOrTypeOrder
      countLamInner lamStack (LamAbs _a _n _ty body) =
        -- If the term is a term lambda abstraction, add it to the list, and
        -- keep on examining the body.
        countLamInner (lamStack <> [MkTerm]) body
      countLamInner lamStack (TyAbs _a _n _kind body) =
        -- If the term is a type lambda abstraction, add it to the list, and
        -- keep on examining the body.
        countLamInner (lamStack <> [MkType]) body
      countLamInner lamStack _ =
        -- Whenever we encounter a body that is not a lambda abstraction, we are done counting
        lamStack

-- | A record for each call sites of a variable.
data ApplicationOrder ann =
  MkApplicationOrder {
    annotation         :: ann -- ^ The annotation of the call site.
    , applicationOrder :: TermOrTypeOrder -- ^ The sequence of term of type applications applied to
    -- this call site.
  }

-- | A mapping of a variable's unique name to a list of `ApplicationOrder` for each of its call
-- sites.
type ApplicationMap ann name = Map.Map name [ApplicationOrder ann]

-- | Counts the number of type and term applications in the let body, including all its subterms,
-- and returns an `ApplicationMap`.
countApp ::
    Ord name => -- needed for `Map`
    Term tyname name uni fun ann -- ^ The `body` of the `Let` term.
    -> ApplicationMap ann name
countApp = countLocal [] Map.empty
    where
      countLocal ::
        Ord name =>
        TermOrTypeOrder -- ^ The application order.
        -> ApplicationMap ann name -- ^ The stack of called variables.
        -> Term tyname name uni fun ann -- ^ The rhs term that is being counted.
        -> ApplicationMap ann name
      countLocal appStack calledStack = go
        where
          go (Apply _ _ fnBody) =
            -- If the term is a term application, add it to the application stack, and
            -- keep on examining the body.
            countLocal (appStack <> [MkTerm]) calledStack fnBody
          go (TyInst _ fnBody _) =
            -- If the term is a type application, add it to the application stack, and
            -- keep on examining the body.
            countLocal (appStack <> [MkType]) calledStack fnBody
          go (Var ann name) =
            -- When we encounter a body that is a variable, we have found a call site of it.
            -- Using `insertWith` ensures that if a variable is called more than once, the new
            -- `ApplicationOrder` map will be appended to the existing one.
            Map.insertWith (<>) name [MkApplicationOrder ann appStack] calledStack
          go (Let _ _ bds letBody) =
            -- recursive or not, the bindings of this let term *may* contain the variable in
            -- question, so we need to check all the bindings and also the body
            let
              -- get the list of rhs's of the term bindings
              getRHS :: Binding tyname name uni fun a -> Maybe (Term tyname name uni fun a)
              getRHS (TermBind _ _ _ rhs) = Just rhs
              getRHS _ =
                -- no need to keep track of the type bindings. Even though this type variable may be
                -- called in the body, it does not affect the resulting `ApplicationMap`
                Nothing
              listOfRHSOfBindings = mapMaybe getRHS (toList bds)
            in
            foldr (flip $ countLocal []) (countLocal [] calledStack letBody) listOfRHSOfBindings
          go (TyAbs _ _ _ tyAbsBody) =
            -- start count in the body of the type lambda abstraction
            countLocal [] calledStack tyAbsBody
          go (LamAbs _ _ _ fnBody) =
            -- start the count in the body of the term lambda abstraction
            countLocal [] calledStack fnBody
          go (Constant _ _) =
            calledStack -- constants cannot call the variable
          go (Builtin _ _) =
            -- default builtin functions in `PlutusCore/Default/Builtins.hs`
            -- cannot call the variable
            calledStack
          go (Unwrap _ tm) =
            countLocal [] calledStack tm
          go (IWrap _ _ _ tm) =
            countLocal [] calledStack tm
          go (Error _ _) = calledStack

