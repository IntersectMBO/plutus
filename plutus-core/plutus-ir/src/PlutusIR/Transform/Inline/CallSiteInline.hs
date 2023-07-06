{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}

{- |
Call site inlining machinery. For now there's only one part: inlining of fully applied functions.
We inline fully applied functions if the cost and size are acceptable.
See note [Inlining of fully applied functions].
-}
module PlutusIR.Transform.Inline.CallSiteInline where

import PlutusCore qualified as PLC
import PlutusCore.Rename
import PlutusCore.Rename.Internal (Dupable (Dupable))
import PlutusIR.Analysis.Size
import PlutusIR.Contexts
import PlutusIR.Core
import PlutusIR.Transform.Inline.Utils
import PlutusIR.Transform.Substitute

import Control.Monad.State

{- Note [Inlining and beta reduction of fully applied functions]

We inline if (1) a function is fully applied (2) its cost and size are acceptable. We discuss
each in detail below.

(1) What do we mean by "fully applied"?

A function is fully applied when it has been applied to all arguments as indicated by its
"syntactic arity":

Consider `let v = rhs in body`, in which `body` calls `v`.

We focus on cases when `v` is a function. (Non-functions have arity () or 0).
I.e., it has type/term lambda abstraction(s). E.g.:

let v = \x1.\x2...\xn. v_body in body

(x1,x2...xn) or n is the syntactic arity of a term. That is, a record of the arguments that the
term expects before it may do some work. Since we have both type and lambda
abstractions, this is not a simple argument count, but rather a list of values
indicating whether the next argument should be a term or a type.

Note that this just corresponds to the number of
syntactic lambda and type abstractions on the outside of the term. It is thus
an under-approximation of how many arguments the term may need.
e.g. consider the term @let id = \x -> x in id@: the variable @id@ has syntactic
arity @[]@, but does in fact need an argument before it does any work.

In `body`, where `v` is called,
if it was given the `n` term or type arguments in the correct order, then it is *fully applied*.
If the changes in size and cost caused by the inlining is acceptable, and the inlining and
the beta reduction is effect-safe, we inline the call site of the fully applied `v`, and perform
beta reduction. E.g.

let f = \x.\y -> x
in
  let z = f q
  in f a b

becomes

let f = \x.\y -> x
in
  let z = f q
  in a

Note that because `f` occurs twice in the original term, and the RHS of `f` is not small enough,
`f` is not unconditionally inlined. Instead, the second usage of `f` is inlined. The first
usage is not inlined because it is not fully applied.

(2) How do we decide whether a fully saturated application can be inlined?

For size, we compare the sizes (in terms of AST nodes before and after the inlining and beta
reduction), and inline only if it does not increase the size. In the above example, we count
the number of AST nodes in `f a b` and in `a`. The latter is smaller, which means inlining
reduces the size.

We care about program size increases primarily because it
affects the size of the serialized script, which appears on chain and must be paid for.
This is different to many compilers which care about this also because e.g. larger ASTs
slow down compilation. We care about this too, but the serialized size is the main driver for us.

The number of AST nodes is an approximate rather than a precise measure. It correlates,
but doesn't directly map to the size of the serialised script. Different kinds of AST nodes
may take different number of bits to encode; in particular, a `Constant` node always
counts as one AST node, but the constant in it can be of arbitrary size. Then, would it be
better to use the size of the serialised term, instead of the number of AST nodes? Not
necessarily, because other transformations, such as CSE, may change the size further;
specifically, if a large constant occurs multiple times in a program, it may get CSE'd.

In general there's no reliable way to precisely predict the size impact of an inlining
decision, and we believe the number of AST nodes is in fact a good approximation.

For cost, we check whether the RHS (in this example, `\x. \y -> x`) has a small cost.
If the RHS has a non-zero arity, then the cost is always small (since a lambda or a type
abstraction is already a value). This may not be the case if the arity is zero.

For effect-safety, we require: (1) the RHS be pure, i.e., evaluating it is guaranteed to
not have side effects; (2) all arguments be pure, since otherwise it is unsafe to
perform beta reduction.
-}

{- | Computes the 'Utils.Arity' of a term. Also returns the function body, for checking whether
it's `Utils.acceptable`.
-}
splitParams ::
  Term tyname name uni fun ann ->
  (Arity tyname name, Term tyname name uni fun ann)
splitParams = \case
  LamAbs _ n _ body ->
    let (nextArgs, nextBody) = splitParams body in (TermParam n : nextArgs, nextBody)
  TyAbs _ n _ body ->
    let (nextArgs, nextBody) = splitParams body in (TypeParam n : nextArgs, nextBody)
  -- Whenever we encounter a body that is not a lambda or type abstraction, we are done counting
  tm -> ([], tm)

{- | Fully apply the RHS of the given variable to the given arguments, and beta-reduce
the application, if possible.
-}
fullyApplyAndBetaReduce ::
  forall tyname name uni fun ann.
  (InliningConstraints tyname name uni fun) =>
  -- | The variable
  VarInfo tyname name uni fun ann ->
  -- | The arguments
  AppContext tyname name uni fun ann ->
  InlineM tyname name uni fun ann (Maybe (Term tyname name uni fun ann))
fullyApplyAndBetaReduce info args0 = do
  -- must rename rhs *before* splitting out the parameters so that the lambdas and their variables
  -- are synced up. substitution.
  rhs <- liftDupable (let Done rhs = varRhs info in rhs)
  let -- split the rhs to its lambdas and function body
      (varArity, rhsBody) = splitParams rhs
      -- | Drop one term or type lambda abstraction of the given term.
      getFnBody :: Term tyname name uni fun ann -> Term tyname name uni fun ann
      getFnBody (LamAbs _ann _n _ty body) = body
      getFnBody (TyAbs _ann _n _kd body)  = body
      getFnBody tm                        = tm
      go ::
        -- | The rhs of the variable
        Term tyname name uni fun ann ->
        Arity tyname name ->
        AppContext tyname name uni fun ann ->
        InlineM tyname name uni fun ann (Maybe (Term tyname name uni fun ann))
      go acc arity args = case (arity, args) of
        -- fully applied
        ([], _) -> pure $ Just acc
        (TermParam param: arity', TermAppContext arg _ args') -> do
          safe <- safeToBetaReduce param arg
          if safe -- we only do substitution if it is safe to beta reduce
            then do
              acc' <- do
                termSubstNamesM -- substitute the term param with the arg in the function body
                  -- rename before substitution to ensure global uniqueness
                  (\n -> if n == param then Just <$> PLC.rename arg else pure Nothing)
                  (getFnBody acc) -- drop one term lambda
              go acc' arity' args'
            else pure Nothing
        (TypeParam param: arity', TypeAppContext arg _ args') -> do
          acc' <-
            termSubstTyNamesM -- substitute the type param with the arg
              (\n -> if n == param then Just <$> PLC.rename arg else pure Nothing)
              (getFnBody acc) -- drop one type lambda
          go acc' arity' args'
        _ -> pure Nothing

      -- Is it safe to turn `(\a -> body) arg` into `body [a := arg]`?
      -- The criteria is the same as the criteria for inlining `a` in
      -- `let !a = arg in body`.
      safeToBetaReduce ::
        -- `a`
        name ->
        -- `arg`
        Term tyname name uni fun ann ->
        InlineM tyname name uni fun ann Bool
      safeToBetaReduce a arg = shouldUnconditionallyInline Strict a arg rhsBody
  go rhsBody (varArity info) args0

-- | Consider whether to inline an application.
inlineSaturatedApp ::
  forall tyname name uni fun ann.
  (InliningConstraints tyname name uni fun) =>
  Term tyname name uni fun ann ->
  InlineM tyname name uni fun ann (Term tyname name uni fun ann)
inlineSaturatedApp t
  | (Var _ann name, args) <- splitApplication t =
      gets (lookupVarInfo name) >>= \case
        Just varInfo ->
          fullyApplyAndBetaReduce varInfo args >>= \case
            Just fullyApplied -> do
              let Done (Dupable rhs) = varRhs varInfo
                  -- Inline only if the size is no bigger than not inlining.
                  sizeIsOk = termSize fullyApplied <= termSize t
                  -- The definition itself will be inlined, so we need to check that the cost
                  -- of that is acceptable. Note that we do _not_ check the cost of the _body_.
                  -- We would have paid that regardless.
                  -- Consider e.g. `let y = \x. f x`. We pay the cost of the `f x` at
                  -- every call site regardless. The work that is being duplicated is
                  -- the work for the lambda.
                  costIsOk = costIsAcceptable rhs
              -- check if binding is pure to avoid duplicated effects.
              -- For strict bindings we can't accidentally make any effects happen less often
              -- than it would have before, but we can make it happen more often.
              -- We could potentially do this safely in non-conservative mode.
              rhsPure <- isTermBindingPure (varStrictness varInfo) rhs
              pure $ if sizeIsOk && costIsOk && rhsPure then fullyApplied else t
            Nothing -> pure t
        -- The variable maybe a *recursive* let binding, in which case it won't be in the map,
        -- and we don't process it. ATM recursive bindings aren't inlined.
        Nothing -> pure t
  | otherwise = pure t
