---
layout: page
title: Table of Contents
---

The Formalisation is split into several sections:

1. [Types](#types)
2. [Normalisation of types](#normal-types)
3. [Builtin machinery](#builtins)
4. [Declarative terms](#declarative-syntax)
5. [Algorithmic terms](#algorithmic-syntax)
6. [Well-scoped types and terms](#extrinsically-typed-syntax-aka-well-scoped-terms)
7. [A typechecker](#type-checker)
8. [Untyped terms](#untyped-terms)
9. [An executable](#executable)


## Types

Type syntax, renaming and substitution, a reduction algorithm (not
used) and a definition of type equality.

```
import Type
import Type.RenamingSubstitution
import Type.Reduction
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

