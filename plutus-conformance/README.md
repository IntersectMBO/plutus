# Plutus Core Conformance Test Suite

**Note: This package is a work-in-progress.**

This package aims to provide an official and comprehensive test suite that checks that the behaviour of Plutus conforms with the specified behaviour. We run all the tests in our CI to ensure continuous conformance. Users are encourage to contribute test cases to this collection of tests and utilize the suite (e.g., running the tests on alternative implementations of Plutus Core).

## Specification

The tests currently cover or will cover the Haskell and Agda implementation of:

- UPLC evaluation
- Typechecking for TPLC, including checking of alpha equivalence. (`tplc-typecheck-test`)
- TPLC evaluation
- Erasure of TPLC to UPLC
- Coverage test
<!-- - Costing conformance? -->

## Adding/updating test outputs

To update test outputs, use the accept test option of the tests. E.g., to have the test results overwriting the `.expected` files in the Haskell implementation test suite (`haskell-conformance`) , run:

`cabal test haskell-conformance --test-options=--accept`

There is also an executable (`add-test-output`) for adding test output with more refined options:

E.g., run

`cabal run add-test-output .uplc plutus-conformance/uplc/ eval -- --missing`

to have the executable search for files with extension `.uplc` in the /uplc directory that are missing output files. It will evaluate and create output files for them.

Or, to update and add outputs to all files in the /uplc directory, run

cabal run add-test-output .uplc plutus-conformance/uplc/ eval -- --all

For the manual, run:

`cabal run add-test-output -- -h`

## Executable for Haskell implementation

(WIP) `haskell-implementation` is an executable for Haskell implementation CLI testing/usage. 

## The Plutus Conformance Test Suite Library

The library provides functions that users can import and run conformance tests with their own implementation. At the moment the tests can only be run against another Haskell implementation. More support will be added later. Of course, one can wrap an arbitrary executable in Haskell. See an explanation [here](https://www.fpcomplete.com/blog/2017/02/typed-process/) and [the related documentation](https://www.stackage.org/haddock/lts-19.11/typed-process-0.2.10.1/System-Process-Typed.html).

## Untyped Plutus Core Program Evaluation

The UPLC evaluation tests ensure conformance of evaluation of untyped plutus core programs. The expected output may contain:

1. "parse error"

The input files are expected to have the concrete syntax. The expected output will show "parse error" when the parser fails to parse the input file.

2. "evaluation error"

If evaluation fails with an error, the expected output will show "evaluation error".

3. An untyped plutus core program

This means the input file successfully evaluates to the output program as per the specification. The evaluated program is represented in the concrete syntax.

### Testing alternative implementation

In the library We provide a function named `runUplcEvalTests` with the following signature:

```haskell
import UntypedPlutusCore.Core.Type qualified as UPLC

type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

runUplcEvalTests :: (UplcProg -> Maybe UplcProg) -> IO ()
```

Users can call this function with their own `runners` with the signature:

```haskell
runner :: (UplcProg -> Maybe UplcProg)
```

The runner should evaluate a UPLC program and return a `Maybe UplcProg`. Given a UPLC program, the runner should return the evaluated program. In case of evaluation failure, the runner should return `Nothing`.

<!-- 
### Type checker

The type checker synthesizes the kind of a given type and the type of a given term. This does not involve any form of inference as Plutus Core is already fully typed. It merely checks the consistency of all variable declarations and the well-formedness of types and terms, while deriving the kind or type of the given type or term.

NB: The type checker requires terms to meet the global uniqueness property. If this is not a given, use a renamer pass to suitably pre-process the term in question.

The `plc` executable can be used to type check programs. Run `cabal run plc typecheck -- -h` in the plutus directory for a full list of options.
 -->

## Contributing

We welcome contributions and comments to this repository. Feel free to open an issue. 

If we add the tests you share, we will acknowledge your contribution and post a link back to your repository. 

## Acknowledgement

We are grateful to these external partners for their contributions:

- Runtime Verification Inc. ([runtimeverification/plutus-core-semantics](https://github.com/runtimeverification/plutus-core-semantics/tree/master/tests))

