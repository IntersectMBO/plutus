# plutus-metatheory
* Mechanised meta theory for Plutus Core *

Plutus Core is the language Plutus programs are compiled into. It is
based on System F omega with iso-recursive types.

Meta theory is theory about the theory. It seeks to answer the
questions of whether the language and its semantics are correct rather
than whether a particular program is correct.

This repository contains a formalisation of Plutus Core in Agda. Agda
is both a dependently typed functional programming language and a
proof assistant. It is particularly suited to formalising programming
languages.

The formalisation requires Agda version 2.5.4.1 or higher.

The formalisation currently covers System F omega with iso recursive
types: the core of Plutus Core. Progress and preservation have been
proven for the language and it is possible to run small
examples. Current work is focused on scaling up the formalisation to
full Plutus Core.

The formalisation is split into three sections. Firstly,

1. Types

Then, two different implementations of the term language:

2. Terms indexed by syntactic types
3. Terms indexed by normal types

## Types

Types are defined the [Type](Type.lagda) module. They are
intrinsically kinded so it is impossible to apply a type operator to
arguments of the wrong kind.

The type module is further subdivided into submodules:

1. [Type.RenamingSubstitution](Type/RenamingSubstitution.lagda)
contains the operations of renaming and substitution for types and
their proofs of correctness. These are necessary to, for example,
define the beta rule for types in the equational theory and reduction
relation (described below).

2. [Type.Equality](Type/Equality.lagda) contains the beta-equational
theory of types. This is essentially a specification for the
computational behaviour of types.

3. [Type.Reduction](Type/Reduction.lagda) contains the small step
reduction relation, the progress/preservation results for types, and
an evaluator for types. This result is not used later in the
development but is in the spec.

4. [Type.BetaNormal](Type/BetaNormal.lagda) contains beta normal forms
for types as a separate syntax. Beta normal forms contain no
beta-redexes and guaranteed not to compute any further.

5. [Type.BetaNBE](Type/BetaNBE.lagda) contains a beta normaliser for
types, it is defined in the style of "normalization-by-evaluation"
(NBE) and is guaranteed to terminate. Further submodules define the
correctness proofs for the normalizer and associated operations.

  * [Type.BetaNBE.Soundness](Type/BetaNBE/Soundness.lagda) contains a
proof that normalizer preserves the meaning of the types. Formally it
states that if we normalize a type then the resultant normal form is
equal (in the equational theory) to the type we started with.

  * [Type.BetaNBE.Completeness](Type/BetaNBE/Completeness.lagda)
contains a proof that the if we were to normalize two types that are
equal in the equation theory then we will end up with identical normal
forms.

  * [Type.BetaNBE.Stability](Type/BetaNBE/Stability.lagda) contains a
proof that normalization will preserve syntactic structure of terms
already in normal form.

  *
[Type.BetaNBE.RenamingSubsitution](Type/BetaNBE/RenamingSubstitution.lagda)
contains a version of substitution that works on normal forms and
ensures that the result is in normal form. This works by embedding
normal forms back into syntax, performing a syntactic substitution and
then renormalizing. The file also contains a correctness proof for
this version of substitution.

## Terms indexed by syntactic types

This version is contained in the
[TermIndexedBySyntacticType](TermIndexedBySyntacticType/) folder.

This is a reference implementation with limited scope. We can define
the terms in this way but their use is complicated by a separate
syntactic constructor for type conversion (type cast/coercion). The
version of progress and preservation and the evaluator do not handle
this constructor. Nevertheless this is sufficient to handle examples
which do not require computing the types before applying
beta-reductions. Such as Church/Scott Numerals.

TODO: detailed description.

# Terms indexed by normal types

This version is contained in the
[TermIndexedByNormalType](TermIndexedByNormalType) folder.

This version is able to handle type conversion by using the normalizer
described above to ensure that types are always in normal form. This
means that no conversion constructor is necessary as any two types
which one could convert between are already in identical normal
form. This allows us to define progress, preservation, and
evaluation for the full language of System F omega with iso-recursive
types.

TODO: detailed description.

