# ADR 2: Steppable CEK machine

Date: 2022-10

## Authors

Marty Stumpf <marty.stumpf@iohk.io>  
Ziyang Liu <ziyang.liu@iohk.io>

## Status

Draft

## Context

In order to have a minimal viable product of a debugger for Plutus, we need a CEK machine that will give us more information for debugging than our current one.

Implementing the steppable CEK machine is a non-trivial task and involves some design decisions:

- should the debugging machine be a separate one?
- should we modify the existing CEK machine to support stepping, or implement something entirely new?
- how do we ensure performance and conformance?

## Decision: A separate machine

We came to the conclusion that the debugging machine should be a separate one. The main reason is that we don't want to slow down the production machine.

## Argument: A separate machine

The debugging machine will give the most accurate information if it was the one in production. However, the drawback of that is that we have to care about its performance.

We only care about performance if the steppable CEK machine will *replace* the production machine instead of being a separate one.

Our current CEK machine's performance is sensitive to changes. For example, exporting the `computeCek` function from the module causes the CEK machine to become slower by up to 25%. Refactoring the machine in preparation for the stepper also shows significant slow downs. See [PR#4909](https://github.com/input-output-hk/plutus/pull/4909). We have enough evidence to show that replacing the machine without slow downs is impossible.

We consciously chose to keep up the production CEK machine's performance by adding a separate machine for debugging. We will mitigate the drawback of this by keeping the implementation as close to the production machine as possible.

## Decision: implementing it as a coroutine system

### Coroutines in Haskell

A steppable CEK is a coroutine system.
A coroutine system is composed of multiple computations cooperatively passing data and control to one another.
In this instance, one computation is the user issuing commands like "step forward", and the other is the CEK machine processing the commands and performing actions like interpreting the script being debugged.
We'll refer to them as the "user computation" and the "machine computation" respectively.

A detailed introduction to coroutines in Haskell can be found in [Coroutine Pipelines](https://themonadreader.files.wordpress.com/2011/10/issue19.pdf).
This section gives a brief summary for the reader's benefits.

Coroutines in Haskell can be implemented using the free monad transformer, [FreeT](https://hackage.haskell.org/package/free/docs/Control-Monad-Trans-Free.html#t:FreeT).
The `Coroutine` type used in the above article is isomorphic to `FreeT`.

To use `FreeT f m`, we need two things: a suspension functor `f`, and a base monad `m`.

The suspension functor is a pattern functor that describes the ways the user computation can suspend and pass control to the machine computation.
Each constructor of the suspension functor should thus represent a user request, such as "step forward".
Constructors generally follow a `RequestType request (response -> a)` pattern.

As an example, consider the following suspension functor:

```haskell
data RequestF a
  = StepF UPLCTerm (Maybe UPLCTerm -> a)
  | LogF Text a
  | InputF (Command -> a)
  deriving Functor
```

`StepF` passes a `UPLCTerm` to the machine computation and suspends, requesting the machine computation to progress one step, and send a `Maybe UPLCTerm` back.
`LogF` sends a `Text` to the machine computation (its response type is `()` and is omitted).
`InputF` requests a `Command` from the user.

Note that this pattern is not limited to a single suspension functor and two computations.
Multiple suspension functors and computations can be composed using [coproducts](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/14416CB20C4637164EA9F77097909409/S0956796808006758a.pdf/data-types-a-la-carte.pdf).

The base monad `m` is the monad the machine computation runs in.
The machine computation interprets each request into an `m` action.
It is essentially a natural transformation from the suspension functor to `m`.

Suppose we define a type `SteppableCekM a` as our base monad `m`.
Then the machine computation can be implemented as the following request handler function:

```haskell
handle :: RequestF a -> SteppableCekM a
handle = \case
  StepF term k -> step term >>= pure . k
  LogF text k  -> log text >> pure k
  InputF k     -> input >>= pure . k
```

where `step term`, `log text` and `input` return `SteppableCekM` actions.

We can then use `handle` to construct a monad morphism, interpreting the user computation (a `FreeT` structure) into a `SteppableCekM` action:

```haskell
runSteppableCek :: FreeT RequestF SteppableCekM a -> SteppableCekM a
runSteppableCek userAction = do
  runFreeT userAction >>= \case
    Pure res -> pure res
    Free req -> handle req >>= runSteppableCek
```

To construct the user computation, `FreeT RequestF SteppableCekM`, we first provide helper functions for constructing `RequestF`s and lifting them into the `FreeT`:

```haskell
stepF :: Monad m => UPLCTerm -> FreeT RequestF m (Maybe UPLCTerm)
stepF term = liftF (StepF term id)

logF :: Monad m => Text -> FreeT RequestF m ()
logF text = liftF (LogF text ())

inputF :: Monad m => FreeT RequestF m Command
inputF = liftF (InputF id)
```

then we can implement the user computation like this:

```haskell
userComputation :: UPLCTerm -> FreeT RequestF SteppableCekM ()
userComputation programToDebug = do
  cmd <- inputF
  case cmd of
    Step -> do
      logF "Received Step command"
      mProgram <- stepF programToDebug
      maybe (pure ()) userComputation mProgram
    ...
```

## Implications
