# Plutus Core Conformance Test Suite

**Note: This package is a work-in-progress.**

This package aims to provide an official and comprehensive test suite that checks that the behaviour of Plutus conforms with the specified behaviour. We run all the tests in our CI to ensure continuous conformance. Users are encouraged to contribute test cases to this collection of tests and utilize the suite (e.g., running the tests on alternative implementations of Plutus Core).

## Specification

This suite tests the latest version of Plutus. Testing of older versions may be added in the future.

The tests currently cover or will cover the Haskell and Agda implementation of:

- Untyped Plutus Core (UPLC) evaluation
- Typechecking for Typed Plutus Core (TPLC), including checking of alpha equivalence. (`tplc-typecheck-test`)
- TPLC evaluation
- Erasure of TPLC to UPLC
- Coverage test
- CPU/memory costing of scripts

## Organisation of tests
The tests mostly take the form of golden tests of fairly simple UPLC programs.  The input files for the tests are organised in a tree of directories under the [test-cases](https://github.com/IntersectMBO/plutus/tree/master/plutus-conformance/test-cases) directory.  If a directory in this tree contains one or more subdirectories then any other files in the directory are ignored and the subdirectories are recursively searched for test cases.  If a directory `<name>` has no subdirectories then it is expected to contain a file called `<name>.uplc` and no other files with the `.uplc` extension. The file `<name>.uplc` should contain textual source code for a  UPLC program, and the directory should also contain a file called `<name>.uplc.expected` containing the expected output of the program and a file called `<name>.uplc.budget.expected`containing the expected CPU and memory budgets.  Any other files (for example `README` files) in the directory are ignored.  See the [addInteger-01](https://github.com/IntersectMBO/plutus/tree/master/plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger-01) for an example of the expected format.  To avoid difficulties with case-insensitive filesystems no two subdirectories of a test directory should have names which differ only by case (eg `True` and `true`).

### Adding/updating test outputs

To update or add test outputs, use the accept test option of the tests. E.g., to have the test results overwrite the `.expected` files in the Haskell implementation test suite (`haskell-conformance`) , run:

`cabal test haskell-conformance --test-options=--accept`

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

#### "evaluation failure"

If evaluation fails with an error, the expected output will show "evaluation failure".

#### An untyped plutus core program

This means the input file successfully evaluates to the output program as per the specification. The evaluated program is represented in the concrete syntax.  An evaluator need not produce a program which is precisely syntactically identical to the expected output, but the two should be equal up to whitespace and α-equivalence (ie, renaming of variables).  Thus
```
lam x (lam y x))
```
and
```
(

      lam var1          (  lam    VARIABLE_1707
var1            )
   )
```
are considered to be equal.

### Testing alternative implementations

In the library we provide a function named `runUplcEvalTests` with the following signature:

```haskell
import UntypedPlutusCore.Core.Type qualified as UPLC

type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

type UplcEvaluatorFun res = UplcProg -> Maybe res

data UplcEvaluator =
  UplcEvaluatorWithoutCosting (UplcEvaluatorFun UplcProg)
  | UplcEvaluatorWithCosting (CostModelParams -> UplcEvaluatorFun (UplcProg, ExBudget))

runUplcEvalTests :: UplcEvaluator -> (FilePath -> Bool) -> (FilePath -> Bool) -> IO ()
```

Users can call this function with their own `UplcEvaluatorFun`, which should evaluate a UPLC program and return a `Maybe UplcProg`, or a `Maybe (UplcProg, ExBudget)` if the budget tests are to be performed as well. Given a UPLC program, the runner should return the evaluated program. In case of evaluation failure, the runner should return `Nothing`.  The two arguments of type `FilePath -> Bool` allow selected evaluation and budget tests (the ones for which the function returns `True`) to be ignored if desired.  Note that [Name](https://github.com/IntersectMBO/plutus/blob/f02a8d77cb4f1167dff7f86279f641127873cc0a/plutus-core/plutus-core/src/PlutusCore/Name/Unique.hs#L56) objects contain `Unique` values which wrap an `Int`: these are used to disambiguate duplicated names, and in the conformance tests equality of `Unique` IDs is used to check that programs are identical up to α-equivalence.  `Unique` IDs are generated automatically when a textual program is loaded and are included in the names of variables (eg, `x-182`) in the expected results of the tests.

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
