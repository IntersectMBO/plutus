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

{- Note [Inlining of fully applied functions]

We inline the call site when a function is fully applied AND the cost and size are acceptable.

Consider `let v :: ty = rhs in body`, in which `body` calls `v`.

We consider cases when `v` is a function/lambda abstraction(s). I.e.:

let v :: type = \x1.\x2...\xn.VBody in body

In the `body`, where `v` is *called*,
if it was given `n` arguments, then it is fully applied in the `body`.
We inline the *call site* of the fully applied `v` in this case, i.e.,
we replace `v x_1 ... x_n` in the `body` with `rhs`. E.g.

let f = \x.\y -> x
in
  let z = f q
  in f a b

becomes

let f = \x.\y -> x
in
  let z = f q
  in a

because f is fully applied in the `body`. Our dead code elimination pass should then turn it to`a`,
reducing the code size. What about

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

To do this we need to count the number of type/term lambda abstractions,
so we know how many term/type arguments they have.

We pattern match the _rhs_ with `LamAbs` or `TyAbs` (lambda abstraction for terms or types),
and count the number of lambdas.
Then, in the _body_, we check for term or type application (`Apply` or `TyInst`) of _v_.

If _v_ is fully applied in the body, i.e., if

1. the number of type lambdas equals the number of type arguments applied, and
2. the number of term lambdas equals the number of term arguments applied, and

if other call site inlining conditions are satisfied,
(we currently inline too little, this will be improved later, see below)

we inline _v_, i.e., replace its occurrence with _rhs_ in the _body_.
For the rest of the discussion here we focus on the conditions 1 and 2 only.

Below are some examples that involve a _body_ that is not fully reducible/applied but
following our heuristic is beneficial.

Example 1: function in body

```haskell
let f = \x . x
     g = \y . f
in g a
```

`f` and `g` each has 1 lambda. However, `g`'s _body_ includes `f` which also has a lambda.
Since we only count the number of lambdas, `g` is fully applied, and we inline.
`g a` reduces to `f`, which reduces the amount of code.

Example 2: function as an argument

```haskell
let id :: forall a . a -> a
    id x = x
in id {int -> int} (\x -> x +1)
```

Here we have a type application for a function that takes one type variable.
I.e., it's fully applied in terms of type.
In terms of terms, `id` takes one argument, and is indeed applied to one.
So `id` is fully applied! And we inline it.
Inlining and reducing `id` reduces the amount of code, as desired.

Example 3: function application in _RHS_

```haskell
let f = (\x.\y.x+y) 4
in f 5
```

With beta-reduction, `f` becomes `\y.4+y` and it has 1 lambda.
The _body_ `f 5` is a fully applied function!
We can reduce it to 4+5.
-}
