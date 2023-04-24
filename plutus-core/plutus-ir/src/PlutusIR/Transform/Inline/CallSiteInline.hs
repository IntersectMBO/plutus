{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}

{-|
Call site inlining machinery. For now there's only one part: inlining of fully applied functions.
We inline fully applied functions if the cost and size are acceptable.
See note [Inlining of fully applied functions].
-}

module PlutusIR.Transform.Inline.CallSiteInline where

import Control.Monad.State
import PlutusIR.Core
import PlutusIR.Transform.Inline.Utils

{- Note [Inlining of fully applied functions]

We inline if (1) a function is fully applied (2) its cost and size are acceptable. We discuss
each in detail below.

(1) What do we mean by "fully applied"?

A function is fully applied when it has been applied to all arguments as indicated by its
"syntactic arity":

Consider `let v = rhs in body`, in which `body` calls `v`.

We focus on cases when `v` is a function. (Non-functions have arity () or 0).
I.e., it has type/term lambda abstraction(s). E.g.:

let v = \x1.\x2...\xn.VBody in body

(x1,x2...xn) or n is the syntactic arity of a term. That is, a record of the arguments that the
term expects before it may do some work. Since we have both type and lambda
abstractions, this is not a simple argument count, but rather a list of values
indicating whether the next argument should be a term or a type.

Note that this just corresponds to the number of
syntactic lambda and type abstractions on the outside of the term. It is thus
an under-approximation of how many arguments the term may need.
e.g. consider the term @let id = \x -> x in id@: the variable @id@ has syntactic
arity @[]@, but does in fact need an argument before it does any work.

In the `body`, where `v` is *called*,
if it was given the `n` term or type arguments in the correct order, then it is *fully applied*.
If `VBody` is acceptable in size and cost, we inline the call site of the fully applied `v` in this
case, i.e., we replace `v` in the `body` with `rhs`. E.g.

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
our dead code elimination pass is able to further reduce the code to just `a`.

Because a function can be called in the `body` multiple times and may not be fully applied for all
its calls, we cannot simply keep a substitution map like in `Inline`,
which substitute *all* occurrences of a variable. Instead, we store all in scope variables in a
map, `Utils.NonRecInScopeSet`, with all information needed for inlining saturated functions.

To find out whether a function is fully applied, when we encounter a variable in the `body`,
we find its arity from the `Utils.NonRecInScopeSet` map and compare it with the list
of arguments it has been applied to at that site. If it is fully applied, we inline it there.

Note that over-application of a function would also be inlined. E.g.:

```haskell
let id = \y -> y
     f = \x -> id
 in f x y
```

`f`'s arity is (\x) or 1, but is applied to 2 arguments. We inline `f` in this case if its cost and
size are acceptable.

(2) How do we decide whether cost and size are acceptable?

We currently reuse the heuristics 'Utils.sizeIsAcceptable' and 'Utils.costIsAcceptable'
that are used in unconditional inlining. For

let v = \x1.\x2...\xn.VBody in body

we check `VBody` with the above "acceptable" functions.
The "acceptable" functions are currently quite conservative, e.g.,
we currently reject `Constant` (has acceptable cost but not acceptable size).
We will work on more refined checks (e.g., checking their sizes instead of just rejecting them) to
improve the optimization.
-}

-- | Computes the 'Utils.Arity' of a term. Also returns the function body, for checking whether
-- it's `Utils.acceptable`.
computeArity ::
    Term tyname name uni fun ann
    -> (Arity, Term tyname name uni fun ann)
computeArity = \case
    LamAbs _ _ _ body ->
      let (nextArgs, nextBody) = computeArity body in (TermParam:nextArgs, nextBody)
    TyAbs _ _ _ body  ->
      let (nextArgs, nextBody) = computeArity body in (TypeParam:nextArgs, nextBody)
    -- Whenever we encounter a body that is not a lambda or type abstraction, we are done counting
    tm                -> ([],tm)

-- | A term or type argument.
data Arg tyname name uni fun ann =
  MkTermArg (Term tyname name uni fun ann)
  | MkTypeArg (Type tyname uni ann)

-- | A list of type or term argument(s) that are being applied.
type Args tyname name uni fun ann = [Arg tyname name uni fun ann]

-- | A pair of argument and the annotation of the term being applied to,
-- so a term that was traversed can be built back with `mkApps`.
type ArgsWithAnns tyname name uni fun ann =
  [(Arg tyname name uni fun ann, ann)]

-- | Takes a term or type application and returns the function
-- being applied and the arguments to which it is applied
collectArgs :: Term tyname name uni fun ann
  -> (Term tyname name uni fun ann, ArgsWithAnns tyname name uni fun ann)
collectArgs tm
  = go tm []
  where
    go (Apply ann f a) as      = go f ((MkTermArg a, ann):as)
    go (TyInst ann f tyArg) as = go f ((MkTypeArg tyArg, ann):as)
    go t as                    = (t, as)

-- | Apply a list of term and type arguments to a function in potentially a nested fashion.
mkApps :: Term tyname name uni fun ann
  -> ArgsWithAnns tyname name uni fun ann
  -> Term tyname name uni fun ann
mkApps f ((MkTermArg tmArg, ann) : args) = mkApps (Apply ann f tmArg) args
mkApps f ((MkTypeArg tyArg, ann) : args) = mkApps (TyInst ann f tyArg) args
mkApps f []                              = f

-- | Given the arity of a function, and the list of arguments applied to it, return whether it is
-- fully applied or not.
isFullyApplied :: Arity -> Args tyname name uni fun ann -> Bool
isFullyApplied [] _ = True -- The function needs no more arguments
isFullyApplied (_lam:_lams) [] = False -- under-application
isFullyApplied (hdLams:tlLams) (hdArg:tlArg) =
  case (hdLams, hdArg) of
    (TermParam, MkTermArg _) -> isFullyApplied tlLams tlArg
    (TypeParam, MkTypeArg _) -> isFullyApplied tlLams tlArg
    _                        ->
      -- wrong argument type, i.e., we have an ill-typed term here. It's not what we define as fully
      -- applied. Although if the term was ill-typed before, it will be ill-typed after the
      -- inlining, and it won't make it any worse, so we could consider accepting this.
      False

-- | Consider whether to inline a saturated application.
considerInlineSat :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Term tyname name uni fun ann -- ^ The `body` of the `Let` term.
    -> InlineM tyname name uni fun ann (Term tyname name uni fun ann)
considerInlineSat tm = do
    -- collect all the arguments of the term being applied to
    case collectArgs tm of
      -- if it is a `Var` that is being applied to, check to see if it's fully applied
      (Var _ann name, args) -> do
        maybeVarInfo <- gets (lookupVarInfo name)
        case maybeVarInfo of
          Just varInfo -> do
            let body = varBody varInfo
                def = varDef varInfo
                fullyApplied = isFullyApplied (arity varInfo) (map fst args)
            -- It is the body that we will be left with in the program after we have
            -- reduced the saturated application, so the size increase we will be left
            -- with comes from the body, and that is what we need to check is okay
                bodySizeOk = sizeIsAcceptable body
            -- The definition itself will be inlined, so we need to check that the cost
            -- of that is acceptable. Note that we do _not_ check the cost of the _body_.
            -- We would have paid that regardless.
            -- Consider e.g. `let y = \x. f x`. We pay the cost of the `f x` at every call
            -- site regardless. The work that is being duplicated is the work for the labmda.
                defCostOk = costIsAcceptable def
            -- check if binding is pure to avoid duplicated effects.
            -- For strict bindings we can't accidentally make any effects happen less often than
            -- it would have before, but we can make it happen more often.
            -- We could potentially do this safely in non-conservative mode.
            defPure <- isTermBindingPure (varStrictness varInfo) def
            pure $
              if fullyApplied && bodySizeOk && defCostOk && defPure
              then mkApps def args
              else tm
          -- We should have variable info for everything, but if we don't just give up
          Nothing -> pure tm
      _ -> pure tm
