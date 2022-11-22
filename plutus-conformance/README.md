# Plutus Core Conformance Test Suite

**Note: This package is a work-in-progress.**

This package aims to provide an official and comprehensive test suite that checks that the behaviour of Plutus conforms with the specified behaviour. We run all the tests in our CI to ensure continuous conformance. Users are encouraged to contribute test cases to this collection of tests and utilize the suite (e.g., running the tests on alternative implementations of Plutus Core).

## Specification

This suite tests the latest version of Plutus. Testing of older versions may be added in the future.

The tests currently cover or will cover the Haskell and Agda implementation of:

- UPLC evaluation
- Typechecking for TPLC, including checking of alpha equivalence. (`tplc-typecheck-test`)
- TPLC evaluation
- Erasure of TPLC to UPLC
- Coverage test
<!-- - Costing conformance? -->

## Adding/updating test outputs

To update or add test outputs, use the accept test option of the tests. E.g., to have the test results overwriting the `.expected` files in the Haskell implementation test suite (`haskell-conformance`) , run:

`cabal test haskell-conformance --test-options=--accept`

There is also an executable (`test-utils`) for adding/updating test output to a specific directory:

E.g., run

`cabal run test-utils .uplc plutus-conformance/test-cases/uplc/evaluation eval`

to have the executable search for files with extension `.uplc` in the /uplc directory. It will evaluate and create/update output files for them.

For the manual, run:

`cabal run test-utils -- -h`

## Debugging mode for Agda's implementation of the UPLC evaluator

One can run the following command to get more detailed error messages on the test cases that fail to evaluate in the Agda implementation:

`cabal run test-utils .uplc [targeted directory/test cases] debug`

For example, to debug the test cases related to builtins, run

`cabal run test-utils .uplc plutus-conformance/test-cases/uplc/evaluation/builtin debug`

## Executable for Haskell implementation

(WIP) `haskell-implementation` is an executable for Haskell implementation CLI testing/usage.

## The Plutus Conformance Test Suite Library

The library provides functions that users can import and run conformance tests with their own implementation. At the moment the tests can only be run against another Haskell implementation. More support will be added later. Of course, one can wrap an arbitrary executable in Haskell. See an explanation [here](https://www.fpcomplete.com/blog/2017/02/typed-process/) and [the related documentation](https://www.stackage.org/haddock/lts-19.11/typed-process-0.2.10.1/System-Process-Typed.html).

## Untyped Plutus Core Program Evaluation

The UPLC evaluation tests ensure conformance of evaluation of untyped plutus core programs.

### The CEK machine

Currently we have tested the conformance of UPLC evaluation against our *Haskell* and *Agda* implementations of the CEK machine. Note that we are not testing conformance of a *reducer*. We are testing an *evaluator*. One noticeable difference between a reducer and an evaluator is that a reducer reduces an ill-defined term to an `error` term while an evaluator has a special *error state*. See section 6.1 of our specification for more details. <!--TODO add link to the spec when it's ready. -->

### Expected outputs

The expected output may contain:

#### "parse error"

The input files are expected to have the concrete syntax. The expected output will show "parse error" when the parser fails to parse the input file.

#### "evaluation error"

If evaluation fails with an error, the expected output will show "evaluation error".

#### An untyped plutus core program

This means the input file successfully evaluates to the output program as per the specification. The evaluated program is represented in the concrete syntax.

### Testing alternative implementations

In the library we provide a function named `runUplcEvalTests` with the following signature:

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
- Hachi Security ([HachiSecurity/plc-llvm/tree/main/compiler/test-data/untyped](https://github.com/HachiSecurity/plc-llvm/tree/main/compiler/test-data/untyped))