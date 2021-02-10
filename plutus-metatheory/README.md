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

### Stage 2 (testing producation against Agda model)

- [X] An extrinsically typed evaluator that can be compiled to Haskell;
- [X] Typechecker + compilation to Haskell;
- [X] Automated building under CI;
- [X] Automated testing of evaluation under CI;
- [X] Automated testing of typechecking under CI.
- [X] Automatic geneneration of programs to test using NEAT
- [ ] Published paper.

### Stage 3 (further metatheory)

- [X] Intrinsically typed CK machine;
- [X] Extrinsically typed CK machine;
- [ ] Correspondence between CK executation and reduction;
- [ ] Correspondence between extrinsic and intrinsic semantics;
- [X] Soundness of typechecking;
- [ ] Completeness of typechecking;
- [X] Intrinsic evaluation, compiled to Haskell.
- [ ] Published paper.

## Installation


### To typecheck the formalisation in Agda
The formalisation requires version 2.6.1 or higher of Agda and the latest
corresonnding version of the Agda standard library.

### To compile to Haskell

It also it contains a command line tool called `plc-agda` for
executing plutus core programs. The command line tool is an Agda
program that is compiled to Haskell, it uses Haskell libraries (such
as bytestring) and also borrows the Plutus parser and pretty printer.

The `plc-agda` tool can be installed by running the following commands
starting in the root folder of the `plutus` repository:

With nix:
```
$ nix-shell
$ cabal v2-install plutus-metatheory
```

Without nix:
```
$ cd plutus-metatheory
$ agda --compile --ghc-dont-call-ghc Main.lagda
$ cd ..
$ cabal v2-install plutus-metatheory
```

The `plc-agda` can execute Plutus Core programs. It is intended to
be used for testing the `plc` command against. The tests can be
executed by running the following command from the `plutus` root
folder:

```
$ nix-shell
$ cabal v2-test plutus-metatheory
```

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

See the [table of contents](https://input-output-hk.github.io/plutus-metatheory/) for an explanation of the structure of the formalisation and links to the code.

**The below information is deprecated and is in the process of being
replaced by the table of contents document.**

## Structure of the intrinsically typed formalisation

The intrinsic formalisation is split into three sections. Firstly,

1. Types.

Then, two different implementations of the term language:

2. Terms indexed by syntactic types (declarative);
3. Terms indexed by normal types (algorithmic).

## Types

Types are defined in the
[Type](https://input-output-hk.github.io/plutus-metatheory/Type.html)
module. They are intrinsically kinded so it is impossible to apply a
type operator to arguments of the wrong kind.

The type module is further subdivided into submodules:

1. [Type.RenamingSubstitution](https://input-output-hk.github.io/plutus-metatheory/Type.RenamingSubstitution.html)
contains the operations of renaming and substitution for types and
their proofs of correctness. These are necessary to, for example,
define the beta rule for types in the equational theory and reduction
relation (described below).

2. [Type.Equality](https://input-output-hk.github.io/plutus-metatheory/Type.Equality.html) contains the beta-equational
theory of types. This is essentially a specification for the
computational behaviour of types.

3. [Type.Reduction](https://input-output-hk.github.io/plutus-metatheory/Type.Reduction.html) contains the small step
reduction relation, the progress/preservation results for types, and
an evaluator for types. This result is not used later in the
development but is in the spec.

4. [Type.BetaNormal](https://input-output-hk.github.io/plutus-metatheory/Type.BetaNormal.html) contains beta normal forms
for types as a separate syntax. Beta normal forms contain no
beta-redexes and guaranteed not to compute any further.

5. [Type.BetaNBE](https://input-output-hk.github.io/plutus-metatheory/Type.BetaNBE.html) contains a beta normaliser for
types, it is defined in the style of "normalization-by-evaluation"
(NBE) and is guaranteed to terminate. Further submodules define the
correctness proofs for the normalizer and associated operations.

   1. [Type.BetaNBE.Soundness](https://input-output-hk.github.io/plutus-metatheory/Type.BetaNBE.Soundness.html) contains a
      proof that normalizer preserves the meaning of the types. Formally it
      states that if we normalize a type then the resultant normal form is
      equal (in the equational theory) to the type we started with.
 
   2. [Type.BetaNBE.Completeness](https://input-output-hk.github.io/plutus-metatheory/Type.BetaNBE.Completeness.html)
      contains a proof that the if we were to normalize two types that are
      equal in the equation theory then we will end up with identical normal
      forms.
 
   3. [Type.BetaNBE.Stability](https://input-output-hk.github.io/plutus-metatheory/Type.BetaNBE.Stability.html) contains a
      proof that normalization will preserve syntactic structure of terms
      already in normal form.
 
   4. [Type.BetaNBE.RenamingSubsitution](https://input-output-hk.github.io/plutus-metatheory/Type.BetaNBE.RenamingSubstitution.html)
      contains a version of substitution that works on normal forms and
      ensures that the result is in normal form. This works by embedding
      normal forms back into syntax, performing a syntactic substitution and
      then renormalizing. The file also contains a correctness proof for
      this version of substitution.

Note: Crucially, this development of NBE (and anything else in the
formalisation for that matter) does not rely on any postulates
(axioms). Despite the fact that we need to reason about functions in
several places we do not require appealing to function extensionality
which currently requires a postulate in Agda. In this formalisation
the (object) type level programs and their proofs appear in (object)
terms. Appealing to a postulate in type level proofs would stop term
level programs computing.

## Builtins

There are builtin types of integers and bytestrings.

1. [Builtin.Constant.Type](https://input-output-hk.github.io/plutus-metatheory/Builtin.Constant.Type.html)
contains the enumeration of the type constants.
2. [Builtin.Constant.Term](https://input-output-hk.github.io/plutus-metatheory/Builtin.Constant.Term.html)
contains the enumeration of the term constants at the bottom.
3. [Builtin.Signature](https://input-output-hk.github.io/plutus-metatheory/Builtin.Signature.html)
contains the list of builtin operations and their type signatures. In
the specification this information is contained in the large builtin
table.

The rest of the Builtin machinery: telescopes, and the semantics of
builtins are contained in
[Declarative.Term.Reduction](https://input-output-hk.github.io/plutus-metatheory/Declarative.Term.Reduction.html).

## Terms indexed by syntactic types

This is the standard presentation of the typing rules that one may
find in a text book. We can define the terms easily in this style but
using them in further programs/proofs is complicated by the presence
of a separate syntactic constructor for type conversion (type
cast/coercion). The typing rules are not syntax directed which means
it is not possible to directly write a typechecker for these rules as
their is always a choice of rules to apply when building a
derivation. Hence we refer to this version as declarative rather than
algorithmic.  In this formalisation where conversion is a constructor
of the syntax not just a typing rule this also affects computation as
we don't know how to process conversions when evaluating. In this
version progress, and evaluation do not handle the conversion
constructor. They fail if they encounter it. Nevertheless this is
sufficient to handle examples which do not require computing the types
before applying beta-reductions. Such as Church/Scott Numerals.

1. The [Declarative.Term](https://input-output-hk.github.io/plutus-metatheory/Declarative.Term.html)
module contains the definition of terms. This module has two further submodules:

   1. [Declarative.Term.RenamingSubstitution](https://input-output-hk.github.io/plutus-metatheory/Declarative.Term.RenamingSubstitution.html)
      contains the definitions of substitution for terms that is necessary to
      specify the beta-rules in the reduction relation. This definition and
      those it depends on, in turn, depend on the definitions and correctness
      proofs of the corresponding type level operations.

   2. [Declarative.Term.Reduction](https://input-output-hk.github.io/plutus-metatheory/Declarative.Term.Reduction.html)
      This file contains the reduction relation for terms (also known
      as the small step operational semantics) and the progress proof.
      Preservation is inherent. Note: this version of
      progress doesn't handle type conversions in terms.

2. [Declarative.Evaluation](https://input-output-hk.github.io/plutus-metatheory/Declarative.Evaluation.html)
contains the evaluator the terms. It takes a *gas* argument which is
the number of steps of reduction that are allowed. It returns both a
result and trace of reduction steps or *out of gas*. Note: this
version of evaluation doesn't handle type conversions in terms.

3. [Declarative.Examples](https://input-output-hk.github.io/plutus-metatheory/Declarative.Examples.html)
contains some examples of Church and Scott Numerals. Currently it is
very memory intensive to type check this file and/or run examples.

4. [Erasure](https://input-output-hk.github.io/plutus-metatheory/Declarative.Erasure.html)

## Terms indexed by normal types

This version is able to handle type conversion by using the normalizer
described above to ensure that types are always in normal form. This
means that no conversion constructor is necessary as any two types
which one could convert between are already in identical normal
form. Here the typing rules are syntax directed and we don't have to
deal with conversions in the syntax. This allows us to define
progress, preservation, and evaluation for the full language of System
F omega with iso-recursive types and sized integers and bytestrings.

1. The [Algorithmic.Term](https://input-output-hk.github.io/plutus-metatheory/Algorithmic.Term.html)
module contains the definition of terms. This module has two further submodules:

   1. [Algorithmic.Term.RenamingSubstitution](https://input-output-hk.github.io/plutus-metatheory/Algorithmic.Term.RenamingSubstitution.html)
      contains the definitions of substitution for terms that is
      necessary to specify the beta-rules in the reduction
      relation. This definition and those it depends on, in turn,
      depend on the definitions and correctness proofs of the
      corresponding type level operations. In this version this
      includes depeneding on the correctness proof of the beta
      normalizer for types.

   2. [Algorithmic.Term.Reduction](https://input-output-hk.github.io/plutus-metatheory/Algorithmic.Term.Reduction.html)
      This file contains the reduction relation for terms (also known
      as the small step operational semantics) and the progress proof.
      Preservation is, again, inherent.

2. [Algorithmic.Evaluation](https://input-output-hk.github.io/plutus-metatheory/Algorithmic.Evaluation.html)
contains the evaluator the terms. It takes a *gas* argument which is
the number of steps of reduction that are allowed. It returns both a
result and trace of reduction steps or *out of gas*.

3. [Algorithmic.Examples](https://input-output-hk.github.io/plutus-metatheory/Algorithmic.Examples.html)
contains some examples of Church and Scott Numerals. Currently it is
very memory intensive to type check this file and/or run examples.

We also need to show that the algorithmic version of the type system is sound and complete.

4. [Algorithmic.Soundness](https://input-output-hk.github.io/plutus-metatheory/Algorithmic.Soundness.html)

Programmatically this corresponds to taking a term with normal type
and converting it back to a term with a syntactic type. This
introduces conversions into the term anywhere there a substitution
occurs in a type.

4. [Algorithmic.Completeness](https://input-output-hk.github.io/plutus-metatheory/Algorithmic.Completeness.html)

5. [Erasure](https://input-output-hk.github.io/plutus-metatheory/Algorithmic.Erasure.html) contains erasure to untyped lambda calculus.

Programmatically this correponds to taking a term with a syntactic
type that may contain conversions and normalising its type by
collapsing all the conversions.

# Extrinsically typed version

1. [Syntax](https://input-output-hk.github.io/plutus-metatheory/Scoped.html)
contains the intrinsically scoped but extrinsically typed terms, and
intrinsically scoped but extrinscically kinded types.

2. [Renaming and
Substitution](https://input-output-hk.github.io/plutus-metatheory/Scoped.RenamingSubstitution.html)
contains the operations of renaming and substitution for extrinsically
typed terms, and extrinsically kinded types.

3. [Reduction](https://input-output-hk.github.io/plutus-metatheory/Scoped.Reduction.html) contains the reduction rules, progress and evaluation.

4. [Extrication](https://input-output-hk.github.io/plutus-metatheory/Scoped.Extrication.html)
contains the operations to convert from intrinsically typed to
extrinscally typed syntax.

5. [Erasure](https://input-output-hk.github.io/plutus-metatheory/Scoped.Erasure.html)
contains operations to erase the types yielding untyped terms.
  
  1. [Renaming and
  Substitution](https://input-output-hk.github.io/plutus-metatheory/Scoped.Erasure.RenamingSubstitution.html)
  contains operations to erase the types in extrinsic renamings and
  substitutions yielding untyped renamings and substitutions.

# Untyped version

1. [Syntax](https://input-output-hk.github.io/plutus-metatheory/Untyped.html)
contains intrinsically scoped but untyped lambda calculus extended
with builtins.

2. [Renaming and
Substitution](https://input-output-hk.github.io/plutus-metatheory/Untyped.RenamingSubstitution.html)
contains operations for untyped renaming and substitution.

3. [Reduction](https://input-output-hk.github.io/plutus-metatheory/Untyped.Reduction.html) contains the untyped reduction rules.
