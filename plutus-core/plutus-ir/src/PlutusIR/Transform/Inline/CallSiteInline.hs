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

import Control.Lens (forMOf)
import Control.Monad.State
import Data.Bifunctor (first)
import PlutusIR.Core
import PlutusIR.Transform.Inline.Utils

{- Note [Inlining of fully applied functions]

We inline if (1) a function is fully applied (2) if its cost and size are acceptable. We discuss
each in detail below.

(1) What do we mean by "fully applied"?

A function is fully applied when it has been applied to all arguments of as indicated by its
syntactic arity.

Consider `let v = rhs in body`, in which `body` calls `v`.

We consider cases when `v` is a function. I.e., it has type/term lambda abstraction(s). I.e.:

let v = \x1.\x2...\xn.VBody in body

(x1,x2...xn) is the syntactic arity of a term. That is, a record of the arguments that the
term expects before it may do some work. Since we have both type and lambda
abstractions, this is not a simple argument count, but rather a list of values
indicating whether the next argument should be a term or a type.

Note that this is the syntactic arity, i.e. it just corresponds to the number of
syntactic lambda and type abstractions on the outside of the term. It is thus
an under-approximation of how many arguments the term may need.
e.g. consider the term @let id = \x -> x in id@: the variable @id@ has syntactic
arity @[]@, but does in fact need an argument before it does any work.


In the `body`, where `v` is *called*,
if it was given the `n` term or type arguments in the correct order, then it is *fully applied*.
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
our dead code elimination pass is able to further reduce the code to just `a`.

To find out whether a function is fully applied,
we first need to count the number of type/term lambda abstractions,
so we know how many term/type arguments they have.

We pattern match the _rhs_ with `LamAbs` and `TyAbs` (lambda abstraction for terms or types),
and track the sequence of lambdas.
Then, in the _body_, we track the term and type application (`Apply` or `TyInst`) of _v_.

If _v_ is fully applied in the body, i.e., if the sequence of type and term lambda abstractions is
exactly matched by the corresponding sequence of type and term applications, then
we inline _v_, i.e., replace its occurrence with _rhs_ in the _body_.

Note that over-application of a function would be inlined. An example of over-application:

```haskell
let id = \y -> y
     f = \x -> id
 in f x y
```

`f`'s arity is 1, but is applied to 2 arguments. We inline `f` in this case if its cost and size
are acceptable.

Because a function can be called in the `body` multiple times and may not be fully applied for all
its calls, we cannot simply keep a simple substitution map like in `Inline`,
which substitute *all* occurrences of a variable.

(2) How do we decide whether cost and size are acceptable?

We currently reuse the heuristics 'Utils.sizeIsAcceptable' and 'Utils.costIsAcceptable'
that are used in unconditional inlining. For

let v = \x1.\x2...\xn.VBody in body

we check `VBody` with the above "acceptable" functions.
Note that all `LamAbs` and `TyAbs` are not acceptable in terms of size, but they should have been
counted out already so we should not immediately encounter those in `VBody`.
Also, we currently reject `Constant` (has acceptable cost but not acceptable size).
We may want to check their sizes instead of just rejecting them.
-}

-- | Computes the 'Utils.Arity' of a term. Also returns the function body, for checking whether
-- it's `Utils.acceptable`.
computeArity ::
    Term tyname name uni fun ann
    -> (Arity, Term tyname name uni fun ann)
computeArity = \case
    LamAbs _ _ _ body -> (first ((:) MkTerm) (computeArity body))
    TyAbs _ _ _ body  -> (first ((:) MkType) (computeArity body))
    -- Whenever we encounter a body that is not a lambda or type abstraction, we are done counting
    tm                -> ([],tm)

-- | A term or type argument.
data Args tyname name uni fun ann =
  MkTermArg (Term tyname name uni fun ann)
  | MkTypeArg (Type tyname uni ann)

-- | A list of type or term argument(s) that are being applied.
type ArgOrder tyname name uni fun ann = [Args tyname name uni fun ann]

-- | A pair of argument and the annotation of the term being applied to,
-- so a term that was traversed can be built back with `mkApps`.
type ArgOrderWithAnn tyname name uni fun ann =
  [(Args tyname name uni fun ann, ann)]

-- | Takes a term or type application expression and returns the function
-- being applied and the arguments to which it is applied
collectArgs :: Term tyname name uni fun ann
  -> (Term tyname name uni fun ann, ArgOrderWithAnn tyname name uni fun ann)
collectArgs expr
  = go expr []
  where
    go (Apply ann f a) as      = go f ((MkTermArg a, ann):as)
    go (TyInst ann f tyArg) as = go f ((MkTypeArg tyArg, ann):as)
    go e as                    = (e, as)

-- | Apply a list of term and type arguments to a function in potentially a nested fashion.
mkApps :: Term tyname name uni fun ann
  -> ArgOrderWithAnn tyname name uni fun ann
  -> Term tyname name uni fun ann
mkApps f ((MkTermArg tmArg, ann) : args) = mkApps (Apply ann f tmArg) args
mkApps f ((MkTypeArg tyArg, ann) : args) = mkApps (TyInst ann f tyArg) args
mkApps f []                              = f

enoughArgs :: Arity -> ArgOrder tyname name uni fun ann -> Bool
enoughArgs [] (_argsOrder:_as) = True -- over-application
enoughArgs (_arity:_) [] = False -- under-application
enoughArgs [] [] = True
enoughArgs lamOrder argsOrder =
  -- start comparing from the end because there may be over-application
  case (last lamOrder, last argsOrder) of
    (MkTerm, MkTermArg _) -> enoughArgs (init lamOrder) (init argsOrder)
    (MkType, MkTypeArg _) -> enoughArgs (init lamOrder) (init argsOrder)
    _                     -> False

-- | Inline fully applied functions iff the body of the function is `acceptable`.
inlineSat :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Term tyname name uni fun ann -- ^ The `body` of the `Let` term.
    -> InlineM tyname name uni fun ann (Term tyname name uni fun ann)
inlineSat appOrTyInstTm =
    case appOrTyInstTm of
      -- If the term is a term or type application, check it's applying to a var that we may inline
      Apply _varAnn _fun _arg  -> go appOrTyInstTm
      TyInst _varAnn _fun _arg -> go appOrTyInstTm
      -- otherwise, check all subterms
      _                        -> forMOf termSubterms appOrTyInstTm inlineSat
      where
        go tm = do
            -- collect all the arguments of the term being applied to
            let argsAppliedTo = fst $ collectArgs tm
                args = snd $ collectArgs tm
            case argsAppliedTo of
              -- if it is a `Var` that is being applied to, check to see if it's fully applied
              Var _ann name -> do
                maybeVarInfo <- gets (lookupCalled name)
                case maybeVarInfo of
                  -- the variable maybe a *recursive* let binding, in which case we don't process,
                  -- and it won't be in the map. ATM recursive bindings aren't inlined.
                  Nothing -> pure tm
                  Just varInfo -> do
                    isAcceptable <- acceptable (calledVarBody varInfo)
                    if isAcceptable && enoughArgs (arity varInfo) (map fst args) then do
                      -- if the body of `Var` is `acceptable` and
                      -- it is fully applied (over-application is allowed) then inline it
                      pure $ mkApps (calledVarDef varInfo) args
                    else pure tm
                  -- if the term being applied is not a `Var`, don't inline
              _ -> pure tm
