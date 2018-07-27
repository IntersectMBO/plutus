# Plutus Core Language Library

The Haskell package `language-plutus-core` implements a range of functionality for manipulating Plutus Core programs. The implementation is based on the [Plutus Core language specification](https://github.com/input-output-hk/plutus-prototype/tree/master/docs/plutus-core).

## Specification

### Exported functionality: `Language.PlutusCore`

* Parser and pretty-printer for textual Plutus Core representation as per the Plutus Core specification

* Binary serialisation and deserialisation using the `cborg` package (coordinate with Duncan)

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

The lexer & parser based on Alex & Happy and the pretty printer uses the `prettyprinter` package. Names (identifiers) are interned using uniques as per `Language.PlutusCore.Name`. They are also parameterised with an attribute used differently in different stages.

Parsing, pretty-printing and the AST representation closely follow the Plutus Core specification. AST nodes are parametereised with the same attribute as the embedded names.

### Renamer

The renamer performs scope resolution and replaces all usage occurences of identifiers with their definition. In the case of Plutus Core, identifiers are either term or type variables whose definition assigns a type or kind, respectively. In other words, we can regard the renamer phase as the propagation of kind and type information from the site of the declaration of a term or type variable to all usages positions of those variables.

### Type checker

The type checker computes the kind of a given type and the type of a given term. This does not involve any form of inference as Plutus Core is already fully typed. It merely checks the consistency of all variable declarations and the well-formedness of types and terms, while deriving the kind or type of the given type or term.
