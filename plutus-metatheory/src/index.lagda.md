---
layout: page
title: Table of Contents
---

# Table of Contents

_This documentation has been produced from the code, which is developed as [Literate Agda](https://agda.readthedocs.io/en/latest/tools/literate-programming.html). Consequently, it contains all of the necessary details to recreate and check the formalisation, including compiler options such as:_

```
{-# OPTIONS --rewriting #-}
```

## Introduction

The Formalisation is split into several sections.

The main body of the formalisation involves a intrinsically typed
implementation of Plutus Core (PLC). It contains types, normal types,
builtins, terms indexed by ordinary types, and terms indexed by normal
types. There is a reduction semantics, CK and CEK machines. There are
proofs of various syntactic properties, a normalisation proof for the
type level language, and a progress proof for the term level
reduction semantics.

There are two additional versions of the PLC language beyond the
intrinsically typed treatment. There is an extrinsically typed but
intrinsically scoped version which is used to represent terms prior
to typechecking and also can be executed directly, and there is a
untyped version of PLC which can also be executed directly.

The final two pieces are a type checker which is guaranteed to be
sound and an executable that is intended to be compiled into Haskell.

1. [Types](#types)
2. [Normalisation of types](#normal-types)
3. [Builtin machinery](#builtins)
4. [Declarative terms](#declarative-syntax)
5. [Algorithmic terms](#algorithmic-syntax)
6. [Well-scoped types and terms](#extrinsically-typed-syntax-aka-well-scoped-terms)
7. [Untyped terms](#untyped-terms)
8. [A typechecker](#type-checker)
9. [An executable](#executable)

## Types

The type level language is similar to simply-typed lambda-calculus
with the addition of constants for forall, μ, and builtin
constants. The [`Type`](Type.html) module contains kinds, contexts and
types. Types are intrinsically scoped and kinded and variables are
represented using De Bruijn indices. Parallel renaming and
substitution are implemented in the
[`Type.RenamingSubstitution`](Type.RenamingSubstitution.html) module
and they are shown to be satisfy the functor and relative monad laws
respectively. Equality of types is specified in the
[`Type.Equality`](Type.Equality.html) module. Equality serves as a
specification of type computation and is used in the normalisation
proof.


```
import Type
import Type.RenamingSubstitution
import Type.Equality
```

## Normal Types

Beta normal forms, a beta NBE algorithm and accompanying soundness,
completeness and stability proofs and necessary equipment for
substituting into normal types by embedding back into syntax,
substituting and renormalising.

```
import Type.BetaNormal
import Type.BetaNBE
import Type.BetaNBE.Soundness
import Type.BetaNBE.Completeness
import Type.BetaNBE.Stability
import Type.BetaNBE.RenamingSubstitution
```

## Builtins

Builtins extend the core System F-omega-mu calculus with primitive
types such as integers and bytestrings and operations on them.

```
import Builtin
import Builtin.Constant.Type
```

The types of the built-in operations are defined by a signature.
These types are abstract, and they can be made concrete to obtain the different
notions of type used in the formalisation.

```
import Builtin.Signature
``` 

## Declarative syntax

A version of the syntax of terms, indexed by types, that includes the
so-called conversion rule as a syntactic constructor. This is the most
direct rendering of the typing rules as syntax but it is hard to
execute programs presented in this syntax. No treatment of execution
is given here, instead we introduce an alternative (algorithmic)
syntax without the conversion rule below. This version serves as a
reference/specification and we prove that the more algorithmic syntax
is sound and complete with respect to it.

```
import Declarative
import Declarative.RenamingSubstitution
import Declarative.Erasure

import Declarative.Examples
import Declarative.Examples.StdLib.Function
import Declarative.Examples.StdLib.ChurchNat
import Declarative.Examples.StdLib.Nat
```
## Algorithmic syntax

Terms, reduction and evaluation where terms are indexed by normal
types

```
import Algorithmic
import Algorithmic.RenamingSubstitution
import Algorithmic.Reduction
import Algorithmic.ReductionEC

import Algorithmic.Evaluation
import Algorithmic.Completeness
import Algorithmic.Soundness
import Algorithmic.Erasure
import Algorithmic.Erasure.RenamingSubstitution
import Algorithmic.CC
import Algorithmic.CK
import Algorithmic.CEK

import Algorithmic.Examples
```

Proof for Progress and Determinism of the Reduction Semantics:

```
import Algorithmic.ReductionEC.Progress
import Algorithmic.ReductionEC.Determinism
```

There are proofs of correspondence of the semantics of:
 * Reduction semantics
 * CC machine
 * CK machine
 * (typed) CEK machine

```
--TODO : Finish proofs for SOPs
--import Algorithmic.BehaviouralEquivalence.ReductionvsCC
--import Algorithmic.BehaviouralEquivalence.CCvsCK
--import Algorithmic.BehaviouralEquivalence.CKvsCEK
```
## Extrinsically typed syntax a.k.a. Well Scoped Terms

Extrinsically typed terms, reduction and evaluation

```
import Scoped
import Scoped.RenamingSubstitution
import Scoped.Extrication
import Scoped.Extrication.RenamingSubstitution
```

## Untyped terms

Untyped terms, reduction and evaluation

```
import Untyped
import Untyped.RenamingSubstitution
import Untyped.CEK
```

## Type checker

This takes a well-scoped term and produces an intrinsically typed term
as evidence of successful typechecking.

```
import Check
```

## Executable

This module is compiled to Haskell and then can be compiled by ghc
to produce an executable.

```
import Main
```

