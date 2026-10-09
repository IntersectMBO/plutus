# Plutus Core Conformance Test Suite

**Note: This package is a work-in-progress.**

This package aims to provide an official and comprehensive test suite that
checks that the behaviour of Plutus conforms with the specified behaviour. We
run all the tests in our CI to ensure continuous conformance.  Users are
encouraged to contribute test cases to this collection of tests and utilise the
suite themselves, e.g., by running alternative implementations of Plutus Core
evaluators on the input files and checking that the expected results are
obtained.

## Specification

This suite tests the latest version of Plutus. Testing of older versions may be added in the future.

The tests currently cover or will cover the Haskell and Agda implementation of:

- Untyped Plutus Core (UPLC) evaluation
- CPU/memory costing of scripts
- Coverage test
- Typechecking for Typed Plutus Core (TPLC), including checking of alpha equivalence. (`tplc-typecheck-test`)
- TPLC evaluation
- Erasure of TPLC to UPLC

## Organisation of tests
The tests mostly take the form of golden tests of fairly simple UPLC programs.  The input files for the tests are organised in a tree of directories under the [test-cases](https://github.com/IntersectMBO/plutus/tree/master/plutus-conformance/test-cases) directory.  If a directory in this tree contains one or more subdirectories then any other files in the directory are ignored and the subdirectories are recursively searched for test cases.  If a directory `<name>` has no subdirectories then it is expected to contain a file called `<name>.uplc` and no other files with the `.uplc` extension. The file `<name>.uplc` should contain textual source code for a  UPLC program, and the directory should also contain a file called `<name>.uplc.expected` containing the expected output of the program and a file called `<name>.budget.expected`containing the expected CPU and memory budgets.  Any other files (for example `README` files) in the directory are ignored.  See the [addInteger-01](https://github.com/IntersectMBO/plutus/tree/master/plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/addInteger/addInteger-01) for an example of the expected format.  To avoid difficulties with case-insensitive filesystems no two subdirectories of a test directory should have names which differ only by case (eg `True` and `true`).

### Flat encoding

Most test-case directories also contain a `<name>.flat` file (and a
`<name>.flat.expected` file), containing the `flat`-encoded version of the
`.uplc` (respectively `.uplc.expected`) program in the same directory. 

Some textual test cases may not have flat equivalents: for example there are test cases which
check that the textual parser rejects ill-formed constants (for example a literal bytestring
containing nox-hexadecimal characters or which contains an odd number of hexadecimal digits),
but these may just be unrepresentable in the flat format.

Note also that the `uplc convert` command can be used to convert `.uplc` files to `.flat` files,
but this may not work for some failing programs (for example, a version 1.0.0 program containing
`constr`, which will be rejected by `uplc convert`).  In such cases it will be necessary to 
construct the corresponding `.flat` file by some other means. 

#### Consistency checking
The majority of `.uplc` files are expected to
have a corresponding `.flat` file, and vice versa: the consistency test
(`conformance-consistency`, run in CI)
fails a test-case directory that has one but not the other, as a reminder to
add both when a new test is added.  The exception is directories listed in
the `skippedConsistencyTests` list in
[consistency/Spec.hs](https://github.com/IntersectMBO/plutus/tree/master/plutus-conformance/consistency/Spec.hs),
which are skipped entirely because `.flat` files don't make sense for them
(see above).  If a directory contains both a `.uplc`
file and a `.flat` file then the test also checks that the abstract syntax tree
obtained by parsing the `.uplc` file is identical to that obtained by decoding the `.flat` file,
and similarly for the `.uplc.expected` and `.flat.expected` files (or that both files record exactly the same failure reason).

### Haskell test suites
By default, the UPLC evaluation test suites (`haskell-conformance`,
`haskell-steppable-conformance`, and `agda-conformance`) run their tests
against the textual `<name>.uplc` files.  Passing `--format flat` as a
test option makes them run against the `<name>.flat` files instead (see
[`Format`](https://github.com/IntersectMBO/plutus/tree/master/plutus-conformance/src/PlutusConformance/Common.hs)),
eg:

`cabal test haskell-conformance --test-options "--format flat"`

Test-case directories which don't have a `.flat` file are silently
skipped when `--format=flat` is used.

### Adding/updating test outputs

To update or add test outputs, use the accept test option of the tests. E.g., to have the test results overwrite the `.expected` files in the Haskell implementation test suite (`haskell-conformance`) , run:

`cabal test haskell-conformance --test-options=--accept`

By default this overwrites the `.uplc.expected` (and `.budget.expected`) files, since the tests run against the textual `.uplc` format unless told otherwise; `.flat.expected` files are left untouched. Passing `--format=flat` alongside `--accept` overwrites `.flat.expected` instead: it's set to the `flat`-encoding of the output program on a successful evaluation, or to the same failure-reason text that would appear in a `.uplc.expected` file (eg "evaluation failure") if the evaluation fails.

`cabal test haskell-conformance --test-options="--format=flat --accept"`

## The Plutus Conformance Test Suite Library

The library provides functions that users can import and run conformance tests with their own implementation. At the moment the tests can only be run against another Haskell implementation. More support will be added later. Of course, one can wrap an arbitrary executable in Haskell. See an explanation [here](https://www.fpcomplete.com/blog/2017/02/typed-process/) and [the related documentation](https://www.stackage.org/haddock/lts-19.11/typed-process-0.2.10.1/System-Process-Typed.html).

### Expected outputs for textual `.uplc` files

If a textual `.uplc` file is expected to fail to parse correctly then the `.uplc.expected` file will contain the string  "parse/decode error"

If the file is expected to parse correctly but an error is expected to occur during evaluation then the `.uplc.expected` file will contain the string "evaluation failure".


If the program is expected to parse and execute without error then the
`.uplc.expected file` will contain a textual UPLC program containing the
expected output.

An evaluator need not produce a program which is precisely syntactically
identical to the expected output, but the two should be equal up to whitespace
and α-equivalence (ie, renaming of variables).  Thus ``` lam x (lam y x)) ```
and

``` (

      lam var1          (  lam    VARIABLE_1707
var1            )
   )
```
are considered to be equal.

### Expected outputs for `.flat` files

If evaluation of a `.flat` file is expected to fail then the `.flat.expected`
file will contain the string "parse/decode error" or "evaluation failure",
exactly as for `.uplc.expected` files (see above). If the `.flat` file decodes
and executes correctly, then the `.flat.expected` file will contain the
flat-encoded form of the program result.

## Expected budgets
The test directories also contain `.budget.expected` files.  These indicate the minimum CPU and memory budgets required
to execute the program (in either `.uplc` or `.flat` form: since these are expected to parse/decode to the
same AST the execution budget for both should be the same).  Note that the budgets are calculated using the 
current cost model in the `plutus` repository, which may differ from that currently in use on the 
Cardano chain: in particular, the version in `plutus` may contain costing information for built-in
functions which have not yet been deployed on the chain and so are not accounted for in the on-chain
cost model.  Also, we may from time to time alter the costs of existing functionality, and such 
alterations may take some time to appear on the chain. 

The `.budget.expected` files for succeeding test cases look like this:
```
({cpu: 181308
| mem: 602})
```

For failing test cases the file will contain either "parse/decode error" or "evaluation failure", as for `.uplc.expected`. 

## Testing alternative implementations

Users are free to use their own test harnesses to consume the test cases, but we
also provide some Haskell machinery for running external tools.  In the library
we provide a function named `runUplcEvalTests` with the following signature:

```haskell
import UntypedPlutusCore.Core.Type qualified as UPLC

type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

data EvaluationResult res = BadMachineParameters | DecodeError | EvalFailure | EvalSuccess res

type UplcEvaluatorFun res = UplcProg -> EvaluationResult res

data UplcEvaluator =
  UplcEvaluatorWithoutCosting (UplcEvaluatorFun UplcProg)
  | UplcEvaluatorWithCosting (CostModelParams -> UplcEvaluatorFun (UplcProg, ExBudget))

runUplcEvalTests :: UplcEvaluator -> (FilePath -> Bool) -> (FilePath -> Bool) -> IO ()
```

Users can call this function with their own `UplcEvaluatorFun`, which should
evaluate a UPLC program and return an `EvaluationResult UplcProg`, or an
`EvaluationResult (UplcProg, ExBudget)` if the budget tests are to be performed
as well. Given a UPLC program, the runner should return `EvalSuccess` with the
evaluated program. In case of evaluation failure it should return `EvalFailure`,
and `DecodeError` or `BadMachineParameters` for the other respective failure
modes.  The two arguments of type `FilePath -> Bool` allow selected evaluation
and budget tests (the ones for which the function returns `True`) to be ignored
if desired.  Note that
[Name](https://github.com/IntersectMBO/plutus/blob/f02a8d77cb4f1167dff7f86279f641127873cc0a/plutus-core/plutus-core/src/PlutusCore/Name/Unique.hs#L56)
objects contain `Unique` values which wrap an `Int`: these are used to
disambiguate duplicated names, and in the conformance tests equality of `Unique`
IDs is used to check that programs are identical up to α-equivalence.  `Unique`
IDs are generated automatically when a textual program is loaded and are
included in the names of variables (eg, `x-182`) in the expected results of the
tests.


## Contributing

We welcome contributions and comments to this repository. Feel free to open an issue.

If we add the tests you share, we will acknowledge your contribution and post a link back to your repository.

## Acknowledgement

We are grateful to these external partners for their contributions:

- Runtime Verification Inc. ([runtimeverification/plutus-core-semantics](https://github.com/runtimeverification/plutus-core-semantics/tree/master/tests))
- Hachi Security ([HachiSecurity/plc-llvm/tree/main/compiler/test-data/untyped](https://github.com/HachiSecurity/plc-llvm/tree/main/compiler/test-data/untyped))
