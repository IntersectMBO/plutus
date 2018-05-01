# Plutus Napkin language library


## Specification

### Exported functionality: `Language.Plutus.Napkin`

* Parser and pretty-printer for textual Plutus Napkin representation as per the Plutus Napkin specification

* Binary serialisation and deserialisation using the `cborg` package (coordinate with Duncan)

* Plutus Napkin abstract syntax

* Typechecker

* Evaluator that closely follows the Plutus Napkin specification (the aim is to obviously follow the specification and not efficiency)

### Testing

* Testsuite based on the `hedgehog` and `tasty` packages

* Round trip testing of parser with pretty-printer and serialisation with deserialisation using `hedgehog`

* Tests against sample PN programs

### Documentation

* Comprehensive documentation of all non-trivial functions and types

* API documentation with Haddock


## Design

TBD
