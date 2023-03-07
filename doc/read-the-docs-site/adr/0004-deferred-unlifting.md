# ADR 4: Deferred unlifting in Plutus Core

Date: 2022-11

## Authors

Michael Peyton Jones <michael.peyton-jones@iohk.io>

## Status

Accepted

## Context

A key part of the evaluation of builtin applications in Plutus Core is "unlifting".
Unlifting is the process of taking a Plutus Core term and turning it into a Haskell value of a known type.
For example, we can unlift an integer constant term into the actual Haskell integer it contains.
This is necessary in order to apply the denotation of the builtin being applied, since that is a Haskell function that operates on Haskell types (e.g. integer addition).

However, unlifting can fail: we cannot unlift a _string_ constant into a Haskell integer!
This failure is visible in program execution, since it terminates the program with an error.

The original design of the builtin application machinery performed unlifting of an argument as soon as it was received. 
This meant that unlifting failures would surface at that point, whereas most of the errors that relate to builtin evaluation can only occur once the builtin has all its arguments, since that's when we run the actual function.

For example:
```
[(builtin addInteger) (con string "hello")]
```
would fail (due to the unlifting failure), even though the builtin _never_ receives all its arguments and is never fully evaluated.

The fact that unlifting errors occur early on makes the specification of the behaviour of builtins significantly more complex.
It would be simpler if unlifting errors occurred when the builtin has all its arguments.
We refer to these two alternatives as "immediate" unlifting (the status quo) and "deferred" unlifting.

Deferred unlifting only makes evaluation slightly more lenient: some terms (such as the above example) do not give an error where they would do with immediate unlifting.

## Decision

We decided:
- To switch to deferred unlifting by default in protocol version 7 (Vasil).
- Having observed (after the hard fork) that no script evaluation in the history of the chain relied on immediate unlifting, to remove all support for immediate unlifting from the evaluator.

## Argument

The difference between immediate and deferred unlifting is only visible in quite specific circumstances.
Since builtins are _usually_ fully applied (otherwise they don't do anything!), an unlifting error will usually be forced right away, regardless of whether we use immediate or deferred unlifting.
The only case where this is not true is where the builtin _never_ receives all its arguments, such as the example given above.
More generally, the only case where behaviour differs is _partially applied_ builtins which are applied to _ill-typed arguments_.
This is quite unusual, since users typically write programs that a) do something and b) are well-typed.

Consequently we felt that it was safe to change the default unlifting behaviour.

However, in order to gain the full benefit of simplification, we would like to remove the existence of immediate unlifting entirely.
If historical script evaluations on the chain still rely on immediate unlifting, then we must support it (and specify it!) forever.
However, once the default has changed, if the history of the chain still validates with _deferred_ unlifting, then we know that no historical script evaluations relied on that behaviour. 
At that point we can _unconditionally_ enable deferred unlifting without worrying about not being able to validate the chain.

In theory, there could be outputs locked with script hashes whose behaviour would (if they are ever spent) rely on inmmediate unlifting.
We cannot rule this out, but given that it has never been relevant in the entire history of the chain, we considered this to be extremely unlikely.

## Alternatives

### 1. Status quo

Undesirable, we face the complexity forever.

### 2. Support both versions forever

Arguably even worse than 1, in that we have to maintain and specify both versions forever, so our complexity burden is even greater.

## Implications

This has already been implemented, and the specification has been updated.
It has no further implications for other decisions that we know of.

## Notes

Relevant PRs:
- [Support for both versions of unlifting](https://github.com/input-output-hk/plutus/pull/4516)
- [Choose the unlifting mode based on protocol version](https://github.com/input-output-hk/plutus/pull/4522)
- [Remove immediate unlifting](https://github.com/input-output-hk/plutus/pull/4879)
- [Mainnet script dump test](https://github.com/input-output-hk/plutus/pull/4726)
- [Update PLC specification for deferred unlifting](https://github.com/input-output-hk/plutus/pull/4960)
