# plutus-metatheory
*Mechanised meta theory for Plutus Core*

Plutus Core is the language Plutus programs are compiled into. It is
based on System F omega with iso-recursive types.

Meta theory is theory about the theory. It seeks to answer the
questions of whether the language and its semantics are correct rather
than whether a particular program is correct. To mechanize it is to
get a proof assistant tool to check your proofs for you. This gives
a much higher degree of assurance.

This repository contains a formalisation of Plutus Core in Agda. Agda
is both a dependently typed functional programming language and a
proof assistant. It is particularly suited to formalising programming
languages. Agda programs can be compiled to Haskell and can make use
of Haskell libraries.

## Roadmap

### Stage 1 (basic metatheory)

- [X] Intrinsically typed representation of the syntax (of Plutus Core);
- [X] Intrinsically typed representation of the reduction semantics;
- [X] Formal Proofs of progress and (type) preservation;
- [X] Evaluator that can be run inside Agda;
- [X] Correspondence to untyped syntax;
- [X] Correspondence to untyped (reduction) semantics;
- [X] Published paper.

### Stage 2 (testing production against Agda model)

- [X] An extrinsically typed evaluator that can be compiled to Haskell;
- [X] Typechecker + compilation to Haskell;
- [X] Automated building under CI;
- [X] Automated testing of evaluation under CI;
- [X] Automated testing of typechecking under CI.
- [X] Automatic geneneration of programs to test using NEAT
- [ ] Published paper.

### Stage 3 (further metatheory)

- [X] Intrinsically typed EC reduction;
- [X] Intrinsically typed CK machine;
- [X] Intrinsically typed CEK machine;
- [ ] Correspondence between structural reduction and EC reduction;
- [X] Correspondence between CK executation and reduction (in EC style);
- [X] Correspondence between CK executation and CEK execution;
- [X] Soundness of typechecking;
- [ ] Completeness of typechecking;
- [X] Intrinsic evaluation, compiled to Haskell.
- [ ] Published paper.

### Stage 4 (untyped CEK)

- [X] Untyped CEK machine;
- [X] Testing typed CEK against untyped CEK;
- [ ] Correspondence between typed and untyped CEK;
- [ ] Untyped CEK compiled to production quality Haskell;
- [ ] Published paper.


## Installation

plutus-metatheory is a module inside plutus, so the instructions are
the same as for other plutus components, see the top-level [README](https://github.com/IntersectMBO/plutus).

You can execute the plc-agda command like this:

```
$ cabal run plc-agda
```

To run the tests you can execute:

```
$ cabal test plutus-metatheory
```

To build the documentation as a static site:

```
$ agda-with-stdlib --html --html-highlight=auto --html-dir=html src/index.lagda.md
$ jekyll build -s html -d html/_site
```

Whenever the `*.lagda` files are modified, maintainers have to remember to re-generate the haskell modules manually using the `generate-malonzo-code` command, which is provided by the nix shell. The command is also run automatically as a pre-commit hook before pushing.

## Features:

* The formalisation currently covers the full language of Plutus Core:
  System F omega with (deep) iso-recursive types, and builtin-types
  for integers and bytestrings, reduction, CK and CEK semantics and
  type checking. Progress and preservation have been shown to hold for
  the small-step operational semantics.

* The Agda formalisation contains an executable `plc-agda` which makes
  use of the parser and pretty printer from `plutus-core` in
  conjunction with an interpreter written in Agda. It has the same
  interface as `plc`. It supports evaluation using various reduction
  strategies and type checking.

## Detailed Description

See the site generated from the [Literate Agda](https://plutus.cardano.intersectmbo.org/metatheory/latest) for an explanation of the structure of the formalisation and links to the code.
