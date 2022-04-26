# Plutus Core Conformance Test Suite

**Note: This package is a work-in-progress.**

This package aims to provide an official and comprehensive test suite that checks that the behaviour of Plutus conforms with the specified behaviour. We run all the tests in our CI to ensure continuous conformance. Users are encourage to contribute test cases to this collection of tests and utilize the suite (e.g., running the tests on alternative implementations of Plutus Core).

## Specification

The tests currently covers or will cover:

- An evaluation test suite for UPLC (`uplc-eval-test`)
- A typechecking test suite for TPLC, including checking of alpha equivalence. (`tplc-typecheck-test`)
- An evaluation test suite for TPLC (`tplc-eval-test`)
- A TPLC to UPLC erasure test suite
- Costing conformance 
- Coverage test

<!-- ## Testing alternative implementation

We provide a function  -->

## Untyped Plutus Core Evaluation

The `uplc-eval-test` test suite ensures that the input untyped plutus core programs evaluate to the expected output. The expected output is obtained by evaluating the programs using the CEK machine.

### The CEK machine

We have an executable, `uplc`, that can call the CEK machine to evaluate untyped plutus core programs. Run 

`cabal run uplc evaluate -- -h` 

for a full list of options.

The CEK machine returns an `EvaluationResult` which is either a successfully computed `Term` or a failure:

```haskell
data EvaluationResult a
    = EvaluationSuccess a
    | EvaluationFailure
```

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

