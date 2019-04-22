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
languages.


## Installation

The formalisation requires a [pre-release of Agda
2.6.0](https://hackage.haskell.org/package/Agda-2.5.4.2.20190330/candidate)
and, the latest version of the Agda standard library, and a version of
ghc that is supported by Agda.

It also it contains a command line tool called `plc-agda` for
executing plutus core programs. The command line tool is an Agda
program that is compiled to Haskell, it uses Haskell libraries (such
as bytestring) and also borrows the Plutus parser and pretty printer.

Building it requires the `language-plutus-core` Haskell library from
[here](https://github.com/input-output-hk/plutus). After installing
this (via `cabal`), `plc-agda` can then be built like this:
```
$ agda --compile --ghc-dont-call-ghc Main.lagda
$ cabal install
```

## Status

The formalisation currently covers the full language of Plutus Core:
System F omega with (deep) iso-recursive types, and builtin-types for
sized integers and sized bytestrings. Progress and preservation have
been shown to hold for the small-step semantics. An evaluator can be
used to execute small examples in Agda and also compile them to
Haskell.

The command line tool `plc-agda` does not include a
typechecker. Instead it uses a separate extrinsically typed
evaluator. It is future work to prove that this gives the same results
as the intrinsically typed evaluator on well typed programs.

## Structure

The formalisation is split into three sections. Firstly,

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

There are builtin types of integers and bytestrings. They are both
sized: max/min values for integers and max length for bytestrings.

1. [Builtin.Constant.Type](https://input-output-hk.github.io/plutus-metatheory/Builtin.Constant.Type.html)
contains the enumeration of the type constants.
2. [Builtin.Constant.Term](https://input-output-hk.github.io/plutus-metatheory/Builtin.Constant.Term.html)
contains the enumeration of the sized term constants at the bottom.
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

Programmatically this correponds to taking a term with a syntactic
type that may contain conversions and normalising its type by
collapsing all the conversions.