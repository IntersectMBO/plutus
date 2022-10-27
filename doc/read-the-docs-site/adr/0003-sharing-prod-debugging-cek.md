# ADR 3: Sharing code between the production and debugging CEK machine

Date: 2022-10

## Authors

Marty Stumpf <marty.stumpf@iohk.io>  

## Status

Draft

## Context

In order to have a minimal viable product of a debugger for Plutus, we need a CEK machine that will give us more information for debugging than our current one.

One of the first decision we need to make is: should the debugging machine be a separate one? The debugging machine need to satisfy these requirements:

- we must not compromise the performance of the production machine, and
- the debugging machine must behave the same as the production machine.

There are tradeoffs between these two requirements. If we have a separate machine, the performance of the production machine will be untouched. But there is more scope for us to make mistakes with the new machine.

But if we share code between the two machines, the performance of the production machine may be compromised.

This ADR proposes approaches for the two machines to share code while not compromising performance.

## Decision: Polymorphic compute/return steps

As long as the debugging machine has the same type, we can alter `computeCek`/`returnCek` to be polymorphic over a type-level `Bool` specifying if we’re in debug mode or not. Then we demote it to the term level in the definition of `computeCek`/`returnCek` and branch on the `Bool` thus implementing different logic depending on whether we're in debug mode or not. This promotion to the type level allows us to statically instantiate the `Bool` in an instance and thus make GHC compile the whole worker of the CEK machine twice: once in debug mode and once in production mode. Theoretically, GHC will take care to remove all the dead debug code when in production mode.

### Detailed description with code snippets

Whether we are debugging or not, we will be returning a `CekState`:

```haskell
data CekState uni fun =
    -- the next state is computing
    Computing WordArray (Context uni fun) (Closure uni fun)
    -- the next state is returning
    | Returning WordArray (Context uni fun) (CekValue uni fun)
    -- evaluation finished
    | Terminating (Term NamedDeBruijn uni fun ())

data Closure uni fun = 
  Closure (Term NamedDeBruijn uni fun ()) (CekValEnv uni fun)
```

The computing step is abstracted out to `computeCekStep` with the following signature:

```haskell
computeCekStep
    :: forall uni fun s
    . (Ix fun, PrettyUni uni fun, GivenCekReqs uni fun s)
    => WordArray
    -> Context uni fun
    -> Closure uni fun
    -> CekM uni fun s (CekState uni fun)
```

```haskell
enterComputeCek :: forall uni fun . Bool -> (Term NamedDeBruijn uni fun ()) -> CekM uni fun s (CekState uni fun)
enterComputeCek debug term = computeCekStep term where
    computeCek = if debug then computeCekDebug else computeCekStep
    {-# NOINLINE computeCek #-}  -- Making sure the `if` is only evaluated once.

    computeCekDebug 
        :: Term NamedDeBruijn uni fun ()
        -- | The `SteppableCekM` is the monad for the debugging CEK machine. It may be just `CekM`.
        -> SteppableCekM uni fun s (CekState uni fun) 
    computeCekDebug term = do
        -- `step` is the function to do a computation step. The first step is always computing the given term with an empty closure, nothing spent on the budget etc.
        state <- step (Computing (toWordArray 0) NoFrame (Closure term Env.empty))
        ...

    computeCek
        :: WordArray
        -> Context uni fun
        -> CekValEnv uni fun
        -> Term NamedDeBruijn uni fun ()
        -> CekM uni fun s (CekState uni fun) -- current return type is `CekM uni fun s (Term NamedDeBruijn uni fun ())`. Now the return type is `CekState` with the term wrapped in the `Terminating` constructor.
    computeCekStep (Force _ body) = computeCek body -- same function as our current CEK except for the return type
    <other_clauses>
```

Because when we are not debugging, we are still using basically the same code as our current implementation, the performance should not be affected by much. (Given that the machine is tail-recursive, the additional wrapping of the returned term in the `Terminating` constructor will affect performance in a negligible way.)

### Argument:



## Implications

In summary, we proposed to share code between the production and debugging CEK machine using .... This implies that:

