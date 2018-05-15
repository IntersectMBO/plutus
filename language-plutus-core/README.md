# Plutus Napkin language library


## Specification

### Exported functionality: `Language.PlutusCore`

* Parser and pretty-printer for textual Plutus Core representation as per the Plutus Core specification

* Binary serialisation and deserialisation using the `cborg` package (coordinate with Duncan)

* Plutus Core abstract syntax

* Typechecker

* Evaluator that closely follows the Plutus Core specification (the aim is to obviously follow the specification and not efficiency)

### Testing

* Testsuite based on the `hedgehog` and `tasty` packages

* Round trip testing of parser with pretty-printer and serialisation with deserialisation using `hedgehog`

* Tests against sample PLC programs

### Documentation

* Comprehensive documentation of all non-trivial functions and types

* API documentation with Haddock


## Design

TBD
