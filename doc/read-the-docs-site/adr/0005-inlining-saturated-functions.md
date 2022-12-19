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
See also [PLT-1044](https://input-output.atlassian.net/browse/PLT-1044).

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
To do this we need to do some arity analysis of functions, 
so we know how many term/type arguments they have.

We also need to decide whether or not to inline based on the call site, which we don’t currently.

This ADR records the details of the design decisions we made for implementing 
inlining of saturated functions ([PLT-1146](https://input-output.atlassian.net/browse/PLT-1146)).

## Decision

For a first round of implementation, we are adding a simplified pass. 
We will refine the implementation over time. 
In each round, we benchmark and test and investigate the results.

### Introduction

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

we inline _v_, i.e., replace its occurrence with _rhs_ (**if** other call site inlining
conditions are satisfied. We currently inline too little, this will be improved later, see below).
For the rest of the discuss we focus on the fully applied condition only.

E.g., for

```haskell
let f = \x.\y.x+y in
    f 2 4
```

the _body_ `f 2 4` is a function application of `f`. Since `f` is fully applied, we inline `f`.

### Other examples

The above case is straight forward. But there are other cases that makes it difficult to determine
whether a function is fully applied. E.g.,

```haskell
let f = \x . 1
     g = \y . f
in g a b
```

```haskell
let id :: forall a . a -> a
     id x = x
in id {int -> int} (\x -> x +1)
```

What about function application?

(\x.\y.x+y) 4

With beta-reduction, it becomes

\y.4+y and it has an arity of 1.



## Future plan

After PLT-1146 is done, we will work on improving this pass so that it will catch more cases.

### Add beta-reduction pass

Beta-reduction of rhs is run first. This will catch more functions.

### Add inline size heuristic



### Add more refined heuristic for call site inlining

See [PLT-1041](https://input-output.atlassian.net/browse/PLT-1041).
At the moment we inline any lambda with a trivial body.
This is too aggressive and has been observed to lead to size increases.
We will optimize this further in PLT-1041.

### Further understanding of the optimization

It's important to point out that it is not obvious why inlining saturated functions causes speedups.
We are doing this because we _observed_ the speedup from Plutonomy's implementation.
It would be useful if we could understand what's causing the speedup,
which will enable us to potentially improve the optimization further, or add other optimization.
