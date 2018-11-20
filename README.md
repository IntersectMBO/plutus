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

The formalisation requires Agda version 2.5.4.1 or higher.

## Status

The formalisation currently covers System F omega with (deep)
iso-recursive types and builtin-types for sized integers and sized
bytestrings. Progress and preservation have been shown to hold for the
small-step semantics and an evaluator can be used to execute small
examples.

### Current status
* deep iso-recursive types are implemented but not fully tested;
* builtins are covered only in the syntactic typed version so far;
* builtins integers are modelled as Agda integers and could,
  potentially, be compiled to Haskell integers. Only a subset of the
  integer operations map to real Agda implementations, the rest are treated
  abstractly. It is possible to, for example, increment an arbitrarily
  sized integer;
* builtin bytestrings are modelled abstractly in Agda and could,
  potentially, be compiled to Haskell bytestrings;
* abstract machines/erasure are not yet covered.

## Structure

The formalisation is split into three sections. Firstly,

1. Types.

Then, two different implementations of the term language:

2. Terms indexed by syntactic types;
3. Terms indexed by normal types.

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
[TermIndexedBySyntacticType.Term.Reduction](https://input-output-hk.github.io/plutus-metatheory/TermIndexedBySyntacticType.Term.Reduction.html).

## Terms indexed by syntactic types

This is a reference implementation with limited scope. We can define
the terms easily in this style but using them in further
programs/proofs is complicated by the presence of a separate syntactic
constructor for type conversion (type cast/coercion). In this version
progress, and evaluation do not handle the conversion
constructor. They fail if they encounter it. Nevertheless this is
sufficient to handle examples which do not require computing the types
before applying beta-reductions. Such as Church/Scott Numerals.


1. The [TermIndexedBySyntacticType.Term](https://input-output-hk.github.io/plutus-metatheory/TermIndexedBySyntacticType.Term.html)
module contains the definition of terms. This module has two further submodules:

   1. [TermIndexedBySyntacticType.Term.RenamingSubstitution](https://input-output-hk.github.io/plutus-metatheory/TermIndexedBySyntacticType.Term.RenamingSubstitution.html)
      contains the definitions of substitution for terms that is necessary to
      specify the beta-rules in the reduction relation. This definition and
      those it depends on, in turn, depend on the definitions and correctness
      proofs of the corresponding type level operations.

   2. [TermIndexedBySyntacticType.Term.Reduction](https://input-output-hk.github.io/plutus-metatheory/TermIndexedBySyntacticType.Term.Reduction.html)
      This file contains the reduction relation for terms (also known
      as the small step operational semantics) and the progress proof.
      Preservation is inherent. Note: this version of
      progress doesn't handle type conversions in terms.

2. [TermIndexedBySyntacticType.Evaluation](https://input-output-hk.github.io/plutus-metatheory/TermIndexedBySyntacticType.Evaluation.html)
contains the evaluator the terms. It takes a *gas* argument which is
the number of steps of reduction that are allowed. It returns both a
result and trace of reduction steps or *out of gas*. Note: this
version of evaluation doesn't handle type conversions in terms.

3. [TermIndexedBySyntacticType.Examples](https://input-output-hk.github.io/plutus-metatheory/TermIndexedBySyntacticType.Examples.html)
contains some examples of Church and Scott Numerals. Currently it is
very memory intensive to type check this file and/or run examples.

## Terms indexed by normal types

This version is able to handle type conversion by using the normalizer
described above to ensure that types are always in normal form. This
means that no conversion constructor is necessary as any two types
which one could convert between are already in identical normal
form. This allows us to define progress, preservation, and
evaluation for the full language of System F omega with iso-recursive
types.

1. The [TermIndexedByNormalType.Term](https://input-output-hk.github.io/plutus-metatheory/TermIndexedByNormalType.Term.html)
module contains the definition of terms. This module has two further submodules:

   1. [TermIndexedByNormalType.Term.RenamingSubstitution](https://input-output-hk.github.io/plutus-metatheory/TermIndexedByNormalType.Term.RenamingSubstitution.html)
      contains the definitions of substitution for terms that is
      necessary to specify the beta-rules in the reduction
      relation. This definition and those it depends on, in turn,
      depend on the definitions and correctness proofs of the
      corresponding type level operations. In this version this
      includes depeneding on the correctness proof of the beta
      normalizer for types.

   2. [TermIndexedByNormalType.Term.Reduction](https://input-output-hk.github.io/plutus-metatheory/TermIndexedByNormalType.Term.Reduction.html)
      This file contains the reduction relation for terms (also known
      as the small step operational semantics) and the progress proof.
      Preservation is, again, inherent.

2. [TermIndexedByNormalType.Evaluation](https://input-output-hk.github.io/plutus-metatheory/TermIndexedByNormalType.Evaluation.html)
contains the evaluator the terms. It takes a *gas* argument which is
the number of steps of reduction that are allowed. It returns both a
result and trace of reduction steps or *out of gas*.

3. [TermIndexedByNormalType.Examples](https://input-output-hk.github.io/plutus-metatheory/TermIndexedByNormalType.Examples.html)
contains some examples of Church and Scott Numerals. Currently it is
very memory intensive to type check this file and/or run examples.
