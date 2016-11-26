# Plutus Language Prototype

This repository implements a prototype of the Plutus language, a pure
functional language with user-defined data types and polymorphism. The formal
specification for this language is given in the paper "Formal Specification
of the Plutus Language", and it's main content is recapitulated throughout
the source code in comments, in an attempt to provide a semi-literate
documentation of the code.

The implementation is split into the implementation of the Core language,
which is primarily the domain of evaluation, and the use-facing Plutus proper,
which is primarily the domain of useful syntax and types. The elaboration
modules handle the translation of Plutus into the Core language, as well as
providing, while the interface modules handle interaction with the world
beyond Plutus (including a REPL and the integration tools for blockchain use).

## Running the demo file

Load `Elaboration.REPL` into your GHCi session or whatever other tool you're
using, then call `replFile "src/Demo.pl"`. This will load the file. You can
now interact with a sparse little REPL:

    $> not True
    con[False]()
    
    $> plus (Suc (Suc Zero)) (Suc (Suc Zero))
    con[Suc](con[Suc](con[Suc](con[Suc](con[Zero]()))))
    
    $> map not (Cons True (Cons False Nil))
    con[Cons](con[False]();con[Cons](con[True]();con[Nil]()))
    
    $> map id (Cons True (Cons False Nil))
    con[Cons](con[True]();con[Cons](con[False]();con[Nil]()))
    
    $> map (\x -> x) (Cons True (Cons False Nil))
    con[Cons](con[True]();con[Cons](con[False]();con[Nil]()))

## To Do / Notes

NOTE: This implementation lacks primitive types and a specific built-in
functions, which will be added when consensus is reached on which are desired.

- Indent/whitespace parsing
- Primitive types and built-in functions
  needs consensus from Serokell team
- instances: Binary, Eq, Show, NFData for Core.Term and Core.Program
- Probably: eliminate `let`s from the core language, replace it with lambda
  lifting so that let definitions can be recursive, and the core language is
  simpler. This will probably need a way to track the provenance of such
  lifted functions, at least for error reporting during type checking?
- Probably: elaborate all the type signatures for declared names first, so
  that mutually recursive functions can be defined