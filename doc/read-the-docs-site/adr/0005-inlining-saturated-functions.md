# ADR 5: Inlining fully saturated functions

Date: 2022-12

## Authors

Marty Stumpf <marty.stumpf@iohk.io>

## Status

Accepted

## Context

As part of our effort to increase script capacity,
we take from [Plutonomy](https://github.com/well-typed/plutonomy),
which gives 15-30% speedup on benchmarks.
See [PLT-1044](https://input-output.atlassian.net/browse/PLT-1044).

The goal is to integrate what we know already works there and
also add optimizations we can do before UPLC (Plutonomy only applies optimization to UPLC).
We currently have an inliner pass for PIR and UPLC.
One of the optimization we can add is inlining of saturated functions in both PIR and UPLC.
From our analysis, this is one of the optimizations that contributes to the speedup in Plutonomy.

For example:

```haskell
let f x y = 1
    y = f q
in f a b 
```

we should inline `f` on line 3 (even though it’s used more than once), because it’s saturated,
i.e. it has all its arguments, and we can reduce it.
([PLT-1146](https://input-output.atlassian.net/browse/PLT-1146))

To do this we need to do some arity analysis of functions,
so we know how many term/type arguments they have.
We also need to decide whether or not to inline based on the call site, which we don’t currently.

This ADR records the details of the design decisions we made for the arity analysis of functions.
The mechanics of whether or not to inline based on the call site will be covered in a separate ADR.

## Decision

For a first round of implementation, we are adding a simplified pass.
We will refine the implementation over time.
In each round, we benchmark and test and investigate the results.

### The implementation: Counting lambdas

**Arity** is relevant when we talk about a fully applied function.
A fully applied function has an arity of 0.
The arity of a function is the number of arguments it takes minus the number of arguments applied.
E.g., `\x.\y.x+y` has an arity of 2. `(\x.\y.x+y) 1` has an arity of 1.

In this inline pass we check for a binding that is a function and is fully applied in the body.

E.g.,

```haskell
let v = rhs in body
```

We pattern match the _rhs_ with `LamAbs` or `TyAbs` (lambda abstraction for terms or types),
and count the number of lambdas.
Then, in the _body_, we check for term or type application (`Apply` or `TyInst`)of _v_.

If _v_ is fully applied in the body, i.e., if

1. the number of type lambdas equals the number of type arguments applied, and
2. the number of term lambdas equals the number of term arguments applied,

we inline _v_, i.e., replace its occurrence with _rhs_ (**if other call site inlining
conditions are satisfied**. We currently inline too little, this will be improved later, see below).
For the rest of the discussion here we focus on the fully applied condition only.

E.g., for

```haskell
let f = \x.\y.x+y in
    f 2 4
```

the _body_ `f 2 4` is a function application of `f`. Since `f` is fully applied, we inline `f`.

### Cases we miss

The above case is straight forward. But there are other cases that
may not give us the desired result if we just count the lambdas. Below are some examples.

#### Example 1: function in body

```haskell
let f = \x . x
     g = \y . f
in g a
```

`f` and `g` each has arity of 1. However, `g`'s _body_ includes `f` which also has arity of 1.
Since we only count the number of lambdas, `g` is fully applied, and we inline.
But `g a` reduces to `f`, which has arity of 1.
So inlining `g` doesn't give the desired result of a fully reducible term in this case.

#### Example 2: function as an argument

```haskell
let id :: forall a . a -> a
    id x = x
in id {int -> int} (\x -> x +1)
```

Here we have a type application for a function that takes one type variable.
I.e., it's fully applied in terms of type.
In terms of terms, `id` takes one argument, and is indeed applied to one.
So `id` is fully applied! And we inline it.

However, reducing the _body_ `id {int -> int} (\x -> x +1)` leaves us `(\x -> x +1)`,
a function of arity 1, not 0.

In this case, inlining and reducing `id` reduces the amount of code,
so even though it reduces to a not fully applied function, it may be desirable.
Again, we need more sophisticated heuristics to improve the performance of this.

#### Example 3: function application in _RHS_

```haskell
let f = (\x.\y.x+y) 4
in f 5
```

With beta-reduction, `f` becomes `\y.4+y` and it has an arity of 1.
The _body_ `f 5` has arity of 0 and thus is a fully applied function!
However, because the _rhs_ `(\x.\y.x+y) 4` is a function application, not a lambda abstraction,
we won't inline it with the current implementation.

## Future plans

We have plans to improve this pass so that it will catch more cases that are desirable,
and not inline undesirably.

### Add beta-reduction pass

If beta-reduction of _rhs_ is run before this pass, it can catch cases categorized by example 3.

### Add inline size heuristic

If we do some analysis of the inline size, we can better decide whether it's desirable to inline.
Plutonomy also [uses a similar heuristic](https://github.com/well-typed/plutonomy/blob/14b9bd46084db1b785b3a99d55f7f10d38165ee8/src/Plutonomy/Hereditary/Transform.hs#L266).

### Add more refined heuristic for call site inlining

See [PLT-1041](https://input-output.atlassian.net/browse/PLT-1041).
At the moment we inline any lambda with a trivial body.
This is too aggressive and has been observed to lead to size increases.
We will optimize this further in PLT-1041.

### Further understanding of the optimization

It is not obvious why inlining saturated functions causes speedups.
We are doing this because we _observed_ the speedup from Plutonomy's implementation.
It would be useful if we could understand what's causing the speedup,
which will enable us to potentially improve the optimization further, or add other optimizations.
