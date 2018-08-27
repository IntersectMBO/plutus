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

The lexer & parser are based on Alex & Happy and the pretty printer uses the `prettyprinter` package. Names (identifiers) are interned using uniques as per `Language.PlutusCore.Name`. They are also parameterised with an attribute used differently in different stages.

Parsing, pretty-printing and the AST representation closely follow the Plutus Core specification. AST nodes are parametereised with the same attribute as the embedded names.

NB: At this stage, every occurrences of a particular name (identifier lexeme) receives the same unique. Hence, binders can be shadowed according to the scoping rules of Plutus Core.

### Renamer

The renamer performs scope resolution and replaces all usage occurrences of identifiers with their definition. In the case of Plutus Core, identifiers are either term or type variables whose definition assigns a type or kind, respectively. In other words, we can regard the renamer phase as the propagation of kind and type information from the site of the declaration of a term or type variable to all usages positions of those variables.

Moreover, renaming ensures that programs meet the **global uniqueness property**: every unique in a program is only bound exactly once. Hence, there is no shadowing or reusing of names in disjoint scopes anymore after this phase.

If program transformations are performed on renamed programs (such as substitution on subterms with free variables), the global uniqueness property may no longer hold. It is recommended to simply perform all necessary transformations without expecting or reinstating the global uniqueness property in between individual transformation steps. When the final form of the program has been reached (or when a program needs to be type checked), an additional use of the renamer can reinstate the global unqiueness property again.

NB: Whenever the global uniqueness property is not a given, care needs be taken to correctly handle binders. For example, when implementing substitution, we need to ensure that we do not propagate a substitution below a binder matching the susbtituted variable and we need to avoid variable capture (as per standard treatments of names in lambda calculi).

### Type checker

The type checker synthesises the kind of a given type and the type of a given term. This does not involve any form of inference as Plutus Core is already fully typed. It merely checks the consistency of all variable declarations and the well-formedness of types and terms, while deriving the kind or type of the given type or term.

NB: The type checker requires terms to meet the global unqiueness property. If this is not a given, use a renamer pass to suitably pre-process the term in question.

### Evaluation

#### Installation

In order to install executables described below type `stack install language-plutus-core` in your terminal. Once the build finishes, you'll be shown the following lines:

```
Copied executables to ~/.local/bin:
- language-plutus-core-generate-evaluation-test
- language-plutus-core-run-ck
```

#### The CK machine

The CK machine can be used to evaluate programs. For this, feed a type checked program to the `runCk` function defined in the `Language/PlutusCore/CkMachine.hs` module:

```haskell
runCk :: Program TyName Name () -> CkEvalResult
```

It returns a `CkEvalResult` which is either a succesfully computed `Value` (which is a type synonym for `Term`) or a failure:

```haskell
data CkEvalResult
    = CkEvalSuccess (Value TyName Name ())
    | CkEvalFailure
```

There is an executable that runs programs on the CK machine: you can run `language-plutus-core-run-ck` and type a program, the program will be run and the result will be printed.

An examle of usage:

```
echo "(program 0.1.0 [(lam x [(con integer) (con 2)] x) (con 2 ! 4)])" | language-plutus-core-run-ck
```

#### Tests

A term generation machinery sits in the `Language/PlutusCore/TestSupport/Generator.hs` module. It allows to generate terms that contain built-ins (integers, bytestrings, sizes and booleans), constant applications and first-order functions. E.g.

```
[ (lam x_0 [ (con integer) (con 3) ] [ (lam x_1 [ (con integer) (con 3) ] [ [ { (con remainderInteger) (con 3) } [ [ { (con multiplyInteger) (con 3) } x_1 ] x_0 ] ] [ [ { (con addInteger) (con 3) } x_0 ] x_1 ] ]) [ [ { (con divideInteger) (con 3) } [ [ { (con addInteger) (con 3) } x_0 ] x_0 ] ] [ [ { (con multiplyInteger) (con 3) } x_0 ] x_0 ] ] ]) [ [ { (con divideInteger) (con 3) } [ [ { (con subtractInteger) (con 3) } [ [ { (con addInteger) (con 3) } (con 3 ! -1053) ] (con 3 ! 269) ] ] [ [ { (con divideInteger) (con 3) } (con 3 ! -1352) ] (con 3 ! -849) ] ] ] [ [ { { (con resizeInteger) (con 3) } (con 3) } (con 3) ] [ [ { { (con resizeInteger) (con 3) } (con 3) } (con 3) ] (con 3 ! 37) ] ] ] ]
```

The generator makes sure a term is well-typed and keeps track of what it's supposed to evaluate to.

There is an executable that prints a term and the expected result of evaluation. Run it as `language-plutus-core-generate-evaluation-test` and you'll be shown something like

```
(program 0.1.0 [ (lam x_0 [ (con integer) (con 2) ] [ [ { (con lessThanInteger) (con 2) } [ [ { (con divideInteger) (con 2) } x_0 ] [ [ { (con divideInteger) (con 2) } x_0 ] x_0 ] ] ] [ [ { (con remainderInteger) (con 2) } x_0 ] x_0 ] ]) [ [ { (con addInteger) (con 2) } [ [ { { (con resizeInteger) (con 2) } (con 2) } (con 2) ] [ [ { (con subtractInteger) (con 2) } (con 2 ! 26) ] (con 2 ! 63) ] ] ] [ [ { (con multiplyInteger) (con 2) } [ [ { (con divideInteger) (con 2) } (con 2 ! 61) ] (con 2 ! -7) ] ] [ [ { (con subtractInteger) (con 2) } (con 2 ! 16) ] (con 2 ! 74) ] ] ] ])

(abs a (type) (lam x (fun (all a (type) (fun a a)) a) (lam y (fun (all a (type) (fun a a)) a) [ y (abs a (type) (lam x a x)) ])))
```

where the first line is a program, the second line is empty and the third line is the result of evaluation of the program (this is how we represent `False` in PLC). Output is always structured this way: three lines with the second one being empty.
