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

However, if we share code between the two machines, the performance of the production machine may be compromised.

This ADR proposes an approach for the two machines to share code while not compromising performance.

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

We enter either modes via `enterComputeCek`, which takes an extra `Bool` than our current implementation, to indicate whether we are in debugging mode or not:

```haskell
enterComputeCek 
    :: forall uni fun s
    . (Ix fun, PrettyUni uni fun, GivenCekReqs uni fun s)
    => Bool
    -> Context uni fun
    -> Closure uni fun
    -> CekM uni fun s (CekState uni fun)
enterComputeCek debug ctx (Closure term env) =
    -- The initial step is always computing with zero budget, empty context and environment.
    -- `computeCekStep` matches on the `term` and calls `computeCek` or `returnCek` depending on the clause. 
    computeCekStep (toWordArray 0) NoFrame (Closure term Env.empty) where
    
    computeCek
        :: WordArray -- for costing
        -> Context uni fun
        -> Closure uni fun
        -> CekM uni fun s (CekState uni fun)
    computeCek = if debug then computeCekDebug else computeCekStep
    {-# NOINLINE computeCek #-}  -- Making sure the `if` is only evaluated once.

    -- in debugging mode, immediately returns the current `CekState` and halts execution. Debugging mode details to be worked out.
    computeCekDebug 
        :: WordArray
        -> Context uni fun
        -> Closure uni fun
        -> CekM uni fun s (CekState uni fun) 
    computeCekDebug budget ctx (Closure term env) = 
        pure $ Computing budget ctx (Closure term env)

    -- In production mode, `computeCekStep` matches on the term and calls `computeCek` or `returnCek` on a subterm. 
    -- In production mode, `computeCek` calls the original `computeCekStep`, i.e. in production mode `computeCekStep` calls itself through the thin `computeCek` wrapper thus achieving recursion and replicating the old behavior of the CEK machine.
    computeCekStep 
        :: WordArray
        -> Context uni fun
        -> Closure uni fun
        -> CekM uni fun s (CekState uni fun) -- the return type is `CekState` instead of a term.
    computeCekStep unbudgetedSteps ctx (Closure (Force _ body) env) = do -- exactly like in current prod
        !unbudgetedSteps' <- stepAndMaybeSpend BForce unbudgetedSteps -- update costs
        computeCek unbudgetedSteps' (FrameForce ctx) (Closure body env) -- compute again with updated costs and ctx
    <other_clauses> -- there's a lot of code in here! Some clauses call `returnCek`, some `computeCek`, achieving recursive calling similar to our current implementation. 
    
    -- details of `forceEvaluate`, `applyEvaluate` etc to be worked out.

    -- similarly for the returning step

    returnCek = if debug then returnCekDebug else returnCekStep
    {-# NOINLINE returnCek #-}
    
    returnCekDebug = ...

    
    returnCekStep 
        :: forall uni fun s
        . (PrettyUni uni fun, GivenCekReqs uni fun s)
        => WordArray
        -> Context uni fun
        -> CekValue uni fun
        -> CekM uni fun s (CekState uni fun) -- return a state instead of a term
    returnCekStep !unbudgetedSteps NoFrame val = do
    spendAccumulatedBudget unbudgetedSteps
    pure $ Terminating $ dischargeCekValue val --wrap the term in the `Terminating` constructor when returning the term.
    <other_clauses>
```

This trick lets us inline the "step" functions and call them recursively like before. Because when we are not debugging, we are still using basically the same code as our current implementation, the performance should not be affected by much. (Given that the machine is tail-recursive, the additional wrapping of the returned term in the `Terminating` constructor will affect performance in a negligible way.)

## Implications

This is a draft of an idea. There are further details to be worked out in a prototype. The implementor should use their own judgement.

Whether we proceed with this approach or not depends on how the prototyping goes, and its benchmarking results. If we find that the slow down is negligible enough, then we may proceed with this. Otherwise, we proceed with a separate implementation for the debugging machine.
