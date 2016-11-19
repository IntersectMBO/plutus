# Plutus Language Prototype

This repository implements a prototype of the Plutus language, a pure
functional language with user-defined data types and polymorphism. The formal
specification for this language is given in the paper "Formal Specification
of the Plutus Language", and it's main content is recapitulated throughout
the source code in comments, in an attempt to provide a semi-literate
documentation of the code.

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


