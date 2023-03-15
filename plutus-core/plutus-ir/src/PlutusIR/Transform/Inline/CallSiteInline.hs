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

module PlutusIR.Transform.Inline.CallSiteInline where

import Control.Monad.State
import Data.Map.Strict qualified as Map
import PlutusIR.Core
import PlutusIR.Transform.Inline.Utils
import Prettyprinter

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

-- | Computes the 'Arity' of a term.
computeArity ::
    Term tyname name uni fun ann
    -> Arity
computeArity = \case
    LamAbs _ _ _ body -> MkTerm : computeArity body
    TyAbs _ _ _ body  -> MkType : computeArity body
    -- Whenever we encounter a body that is not a lambda or type abstraction, we are done counting
    _                 -> []

-- | Inline fully applied functions iff the body of the function is `acceptable`.
considerInline ::
    Term tyname name uni fun ann -- the variable that is a function
    -> InlineM tyname name uni fun ann (Term tyname name uni fun ann)
considerInline v@(Var ann n) = do
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
        -- if the size and cost are acceptable, then check if it's fully applied
        -- See note [Identifying fully applied call sites].
        else do
          pure v
considerInline _notVar = -- this should not happen
  Prelude.error  "considerInline: should be a variable."

-- | A record for each call sites of a variable.
-- data ApplicationOrder ann =
--   MkApplicationOrder {
--     annotation         :: ann -- ^ The annotation of the call site.
--     , applicationOrder :: AppOrder -- ^ The sequence of term or type applications applied to
    -- this call site.
  -- }

-- | A mapping of a variable's unique name to a list of `ApplicationOrder` for each of its call
-- sites.
-- type ApplicationMap ann name = Map.Map name [ApplicationOrder ann]

data Args tyname name uni fun ann =
  MkTermArg (Term tyname name uni fun ann)
  | MkTypeArg (Type tyname uni ann)

type ArgOrder tyname name uni fun ann = [Args tyname name uni fun ann]

-- | Takes a term or type application expression and returns the function
-- being applied and the arguments to which it is applied
collectArgs :: Term tyname name uni fun ann
  -> (Term tyname name uni fun ann, ArgOrder tyname name uni fun ann)
collectArgs expr
  = go expr []
  where
    go (Apply _ f a) as      = go f (MkTermArg a:as)
    go (TyInst _ f tyArg) as = go f (MkTypeArg tyArg:as)
    go e as                  = (e, as)

-- | Apply a list of term and type arguments to a function in potentially a nested fashion.
mkApps :: Term tyname name uni fun ann
  -> ArgOrder tyname name uni fun ann
  -> Term tyname name uni fun ann
mkApps f (MkTermArg tmArg : args) = Apply  f args

enoughArgs :: Arity -> ArgOrder tyname name uni fun ann -> Bool
enoughArgs [] argsOrder = True
enoughArgs arity [] = False
enoughArgs lamOrder argsOrder =
  -- start comparing from the end because there may be over-application
  case (last lamOrder, last argsOrder) of
    (MkTerm, MkTermArg _) -> enoughArgs (init lamOrder) (init argsOrder)
    (MkType, MkTypeArg _) -> enoughArgs (init lamOrder) (init argsOrder)
    _                     -> False

-- | Inline fully applied functions. See note [Identifying fully applied call sites].
inlineFullyApplied :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Term tyname name uni fun ann -- ^ The `body` of the `Let` term.
    -> InlineM tyname name uni fun ann (Term tyname name uni fun ann)
-- If the term is a term application, get the `AppOrder` of the
inlineFullyApplied appTerm@(Apply _ fun arg) = do
    -- collect all the arguments of the term being applied to
    let argsAppliedTo = fst $ collectArgs appTerm
        args = snd $ collectArgs appTerm
    case argsAppliedTo of
      -- if it is a `Var` that is being applied to, check to see if it's fully applied
      Var _ name -> do
        maybeVarInfo <- gets (lookupCalled name)
        case maybeVarInfo of
          Nothing -> pure $ Apply _ (go fun) (go arg)
          Just varInfo -> do
            if enoughArgs (arity varInfo) args then
              -- if the `Var` is fully applied (over-application is allowed) then inline it
              mkApps (calledVarDef varInfo) (go <$> args)
            else pure $ Apply _ (go fun) (go arg) -- otherwise just keep going
          -- if the term being applied is not a `Var`, just keep going
      _ -> pure $ Apply _ (go fun) (go arg)
inlineFullyApplied (TyInst _ fnBody _) =
    -- If the term is a type application, add it to the application stack, and
    -- keep on examining the body.
    countLocal (appStack <> [MkType]) calledStack fnBody
inlineFullyApplied tm = pure tm

--  (Var ann name) =
--             -- When we encounter a body that is a variable, we have found a call site of it.
--             -- Using `insertWith` ensures that if a variable is called more than once, the new
--             -- `ApplicationOrder` map will be appended to the existing one.
--             Map.insertWith (<>) name [MkApplicationOrder ann appStack] calledStack
--           go (Let _ _ bds letBody) =
--             -- recursive or not, the bindings of this let term *may* contain the variable in
--             -- question, so we need to check all the bindings and also the body
--             let
--               -- get the list of rhs's of the term bindings
--               getRHS :: Binding tyname name uni fun ann -> Maybe (Term tyname name uni fun ann)
--               getRHS (TermBind _ _ _ rhs) = Just rhs
--               getRHS _ =
--                 -- no need to keep track of the type bindings. Even though this type variable
--                 -- called in the body, it does not affect the resulting `ApplicationMap`
--                 Nothing
--               listOfRHSOfBindings = mapMaybe getRHS (toList bds)
--             in
--             foldr (flip $ countLocal []) (countLocal [] calledStack letBody) listOfRHSOfBindings
--           go (TyAbs _ _ _ tyAbsBody) =
--             -- start count in the body of the type lambda abstraction
--             countLocal [] calledStack tyAbsBody
--           go (LamAbs _ _ _ fnBody) =
--             -- start the count in the body of the term lambda abstraction
--             countLocal [] calledStack fnBody
--           go (Constant _ _) =
--             calledStack -- constants cannot call the variable
--           go (Builtin _ _) =
--             -- default builtin functions in `PlutusCore/Default/Builtins.hs`
--             -- cannot call the variable
--             calledStack
--           go (Unwrap _ tm) =
--             countLocal [] calledStack tm
--           go (IWrap _ _ _ tm) =
--             countLocal [] calledStack tm
--           go (Error _ _) = calledStack

