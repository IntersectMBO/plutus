{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeFamilies     #-}

{-|
Call site inlining machinery. For now there's only one part: inlining of fully applied functions.
See ADR TODO for motivation. We inline fully applied functions if the cost and size are acceptable.
See note [Inlining of fully applied functions].
-}

module PlutusIR.Transform.Inline.CallSiteInline where

import PlutusCore.Name
import PlutusIR
import PlutusIR.Transform.Rename ()

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

We pattern match the _rhs_ with `LamAbs` or `TyAbs` (lambda abstraction for terms or types),
and count the number of lambdas.
Then, in the _body_, we check for term or type application (`Apply` or `TyInst`) of _v_.

If _v_ is fully applied in the body, i.e., if

1. the number of type lambdas equals the number of type arguments applied, and
2. the number of term lambdas equals the number of term arguments applied, and

we inline _v_, i.e., replace its occurrence with _rhs_ in the _body_.

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

Example 3: function application in _RHS_

let f = (\x.\y.x+y) 4
in f 5

With beta-reduction, `f` becomes `\y.4+y` and it has 1 lambda.
The _body_ `f 5` is a fully applied function!
We can reduce it to 4+5.

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

-- | For keeping track of term lambda or type lambda of a binding.
data LamKind = TermLam | TypeLam

-- | A list of `LamAbs` and `TyAbs`, in order, of a binding.
type LamOrder = [LamKind]

-- | A mapping of a binding to its term and type lambdas in order.
newtype FnLam tyname name uni fun a =
    MkFnLam (UniqueMap TermUnique LamOrder)
    deriving newtype (Semigroup, Monoid)

-- | Count the number of type and term lambdas in the RHS of a binding and return an ordered list
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
        -- whenever we encounter a body that is not a lambda abstraction, we are done counting
        currLamOrder

{- Note [Inlining a lambda abstraction]
TODO revise Note [Inlining and global uniqueness]
We will be inlining a lambda abstraction when we find a fully applied function.
We follow section 3.2 of the paper:

Consider let v = \x1....\xn.VBody in body


Suppose we write the call subst M [E=x] to mean the result of substituting E for x in M.
The standard rule for substitution when M is a lambda abstraction is:
subst (\x:M ) [E=x] = \x:M
subst (\x:M ) [E=y ] = \x:(subst M [E=y ])
if x does not occur free in E
-}
