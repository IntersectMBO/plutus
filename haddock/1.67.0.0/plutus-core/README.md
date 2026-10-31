# Plutus Core Language Library

The Haskell package `plutus-core` implements a range of functionality for manipulating Plutus Core programs. The implementation is based on the [Plutus Core language specification](../plutus-core-spec).

## Specification

### Exported functionality: `PlutusCore`

* Parser and pretty-printer for textual Plutus Core representation as per the Plutus Core specification

* Binary serialisation and deserialisation using the `flat` package

* Plutus Core abstract syntax

* Renamer

* Type checker

* Evaluator (interpreter based on the CK machine) that closely follows the Plutus Core specification (the aim is to obviously match the specification without much concern for efficiency)

### Testing

* Testsuite based on the `hedgehog` and `tasty` packages

* Round trip testing of parser with pretty-printer and serialisation with deserialisation using `hedgehog`

* Golden tests against sample PLC programs

### Documentation

* Comprehensive documentation of all non-trivial functions and types

* API documentation with Haddock

## Design

### Parser and pretty printer

The parsers are based on Megaparsec and the pretty printer uses the `prettyprinter` package. Names (identifiers) are interned using uniques as per `PlutusCore.Name`. They are also parameterised with an attribute used differently in different stages.

Parsing, pretty-printing and the AST representation closely follow the Plutus Core specification. AST nodes are parameterised with the same attribute as the embedded names.

NB: At this stage, every occurrences of a particular name (identifier lexeme) receives the same unique. Hence, binders can be shadowed according to the scoping rules of Plutus Core.

### Renamer

The renamer performs scope resolution and replaces all usage occurrences of identifiers with their definition. In the case of Plutus Core, identifiers are either term or type variables whose definition assigns a type or kind, respectively. In other words, we can regard the renamer phase as the propagation of kind and type information from the site of the declaration of a term or type variable to all usages positions of those variables.

Moreover, renaming ensures that programs meet the **global uniqueness property**: every unique in a program is only bound exactly once. Hence, there is no shadowing or reusing of names in disjoint scopes anymore after this phase.

If program transformations are performed on renamed programs (such as substitution on subterms with free variables), the global uniqueness property may no longer hold. It is recommended to simply perform all necessary transformations without expecting or reinstating the global uniqueness property in between individual transformation steps. When the final form of the program has been reached (or when a program needs to be type checked), an additional use of the renamer can reinstate the global uniqueness property again.

NB: Whenever the global uniqueness property is not a given, care needs be taken to correctly handle binders. For example, when implementing substitution, we need to ensure that we do not propagate a substitution below a binder matching the substituted variable and we need to avoid variable capture (as per standard treatments of names in lambda calculi).

### Type checker

The type checker synthesizes the kind of a given type and the type of a given term. This does not involve any form of inference as Plutus Core is already fully typed. It merely checks the consistency of all variable declarations and the well-formedness of types and terms, while deriving the kind or type of the given type or term.

NB: The type checker requires terms to meet the global uniqueness property. If this is not a given, use a renamer pass to suitably pre-process the term in question.

The `plc` executable can be used to type check programs. Run `cabal run plc typecheck -- -h` in the plutus directory for a full list of options.

### Evaluation

#### The CK machine

The CK machine can be used to evaluate programs. For this, feed a type checked
Plutus Core term to the `unsafeEvaluateCk` function defined in the
[`PlutusCore.Evaluation.Machine.Ck`](src/PlutusCore/Evaluation/Machine/Ck.hs)
module (the `DynamicBuiltinNameMeanings` argument contains information about
extra built-in functions and can safely be set to `Data.Map.empty` for simple
programs):

```haskell
unsafeEvaluateCk
    :: DynamicBuiltinNameMeanings (CkValue uni)
    -> Term TyName Name uni () -> EvaluationResult (Term TyName Name uni ())
```

It returns an `EvaluationResult` which is either a successfully computed `Term` or a failure:

```haskell
data EvaluationResult a
    = EvaluationSuccess a
    | EvaluationFailure
```
It can also raise an exception, as indicated by `unsafe` in the name, but this should not happen for well-formed programs.

There is an executable that runs programs on the CK machine: you can feed a program to `plc evaluate`, the program will be run and the result will be printed. Run `cabal run plc evaluate -- -h` for a full list of options.

#### The CEK machine

Similarly for untyped plutus core, the CEK machine can be used to evaluate untyped plutus core programs. Run `cabal run uplc evaluate -- -h` for a full list of options.
