---
layout: page
title: Table of Contents
---

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
contants. The [`Type`](Type.html) module containts kinds, contexts and
types. Types are intrinsically scoped and kinded and variables are
represented using De Bruijn indices. Parallel renaming and
substitution are implemented in the
[`Type.RenamingSubstitution`](Type/RenamingSubstitution.html) module
and they are shown to be satisfy the functor and relative monad laws
respectively. The [`Type.Reduction`](Type/Reduction.html) module
contains a small step reduction algorithm for types and the
[`Type.CK`](Type/CK.html) contains a CK machine for
types. Neither are used directly in the formalisation as computation
on types is carried out using normalisation by evaluation
instead. Equality of types is specified in the
[`Type.Equality`](Type/Equality.html) module. Equality serves as a
specification of type compuation and is used in the normalisation
proof.

```
import Type
import Type.RenamingSubstitution
import Type.Equality
import Type.Reduction
import Type.CK
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
import Builtin.Signature
import Builtin.Constant.Type
import Builtin.Constant.Term
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
import Algorithmic.Evaluation
import Algorithmic.Main
import Algorithmic.Completeness
import Algorithmic.Soundness
import Algorithmic.Erasure
import Algorithmic.Erasure.RenamingSubstitution
--import Algorithmic.Erasure.Reduction
import Algorithmic.CK
import Algorithmic.CEKV

import Algorithmic.Examples
```

## Extrinsically typed syntax a.k.a. Well Scoped Terms

Extrinsically typed terms, reduction and evaluation

```
import Scoped
import Scoped.RenamingSubstitution

import Scoped.Reduction

import Scoped.Extrication
import Scoped.Extrication.RenamingSubstitution
--import Scoped.Extrication.Reduction
import Scoped.Erasure
--import Scoped.Erasure.RenamingSubstitution
--import Scoped.Erasure.Reduction
import Scoped.CK
```

## Untyped terms

Untyped terms, reduction and evaluation

```
import Untyped
import Untyped.RenamingSubstitution
import Untyped.Reduction
```

## Type checker

This takes a well-scoped term and produces an intrinsically typed term
as evidence of successful typechecking.

```
import Check
```

## Executable

This module is is compiled to Haskell and then can be compiled by ghc
to produce an executable.

```
import Main
```

