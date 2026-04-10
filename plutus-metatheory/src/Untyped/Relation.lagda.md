---
title: Untyped.Transform
layout: page
---

```
module Untyped.Relation where
open import Function using (case_of_)

open import Untyped
open import Data.Nat
open import Data.Fin
open import Data.List hiding (fromMaybe)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Relation.Binary.PropositionalEquality using (_≡_)
```

## Note on reusing the standard library

We can't reuse `Relation.Binary` from the standard library here because a
relation on terms needs to be aware of the ℕ index that we use for representing
the scope. `Relation.Binary.Indexed.Heterogeneous` on the other hand is a bit
too general because its definitions may have indices that differ (see e.g.
`Transitive`), which makes using it inconvenient to use because Agda cannot
always infer the indices.


## Binary relations on untyped terms

```
Relation : Set₁
Relation = ∀{X} → X ⊢ → X ⊢ → Set
```

## Standard properties

```
Reflexive : Relation → Set
Reflexive _~_ = ∀ {X} {M : X ⊢} →
  -----
  M ~ M

Transitive : Relation → Set
Transitive _~_ = ∀ {X} {L M N : X ⊢} →
  L ~ M →
  M ~ N →
  -------
  L ~ N

Symmetric : Relation → Set
Symmetric _~_ = ∀ {X} {M N : X ⊢} →
  M ~ N →
  -------
  N ~ M

Idempotent : Relation → Set
Idempotent R = ∀ {X} {L M N : X ⊢} → R L M → R M N → M ≡ N
```

## Properties with respect to functions on terms

Operations on terms can be abbreviated:

```
Transform : Set
Transform = ∀{X} → X ⊢ → X ⊢

Transform₂ : Set
Transform₂ = ∀{X} → X ⊢ → X ⊢ → X ⊢
```

A compatible function maps related inputs to related outputs:

```
Compatible₁ : Relation → Transform → Set
Compatible₁ _~_ f =
  ∀ {X} {M N : X ⊢} →
    M ~ N →
    ---------
    f M ~ f N

Compatible₂ : Relation → Transform₂ → Set
Compatible₂ _~_ f =
  ∀ {X} {K L M N : X ⊢} →
    K ~ L →
    M ~ N →
    -------------
    f K M ~ f L N

Compatible' : ∀ {X Y} → Relation →  (X ⊢ → Y ⊢) → Set
Compatible' _~_ f =
  ∀ {M N} →
    M ~ N →
    ---------
    f M ~ f N

```

An extensive function maps an input to a related output. Another way of viewing
this is that the graph of the function (i.e. a set of pairs) is a subset of the
relation (when viewed as set of pairs).

```
-- TODO make M explicit arg
Extensive : Transform → Relation → Set
Extensive f _~_ = ∀ {X} {M : X ⊢} →
  M ~ f M

Extensive? : (∀ {X} → X ⊢ → Maybe (X ⊢)) → Relation → Set
Extensive? f R = ∀ {X} (M : X ⊢) {M' : X ⊢} → f M ≡ just M' → R M M'

_⊆_ : Relation → Relation → Set
R ⊆ S = ∀ {X} {M N : X ⊢} → R M N → S M N

ext?-⊆ : ∀ {f : ∀ {X} → X ⊢ → Maybe (X ⊢)} {R S : Relation} →
  R ⊆ S →
  Extensive? f R →
  Extensive? f S
ext?-⊆ R⊆S ext-f-R M eq = R⊆S (ext-f-R M eq)

-- ext?-ext : ∀{f : ∀ {X} → X ⊢ → Maybe (X ⊢)} {R : Relation} →
--   Extensive? f R →
--   Extensive (λ M → fromMaybe M (f M)) R
-- ext?-ext {f} ext?-f = ?

```

## Structures

```
record Equivalence (_~_ : Relation) : Set where
  field
    refl : Reflexive _~_
    trans : Transitive _~_
    sym : Symmetric _~_

record TermCompatible (_~_ : Relation) : Set where
  field
    compat-var : ∀ {X} {n : Fin X} → ` n  ~ ` n
    compat-ƛ : ∀ {X} {M N : suc X ⊢} → M ~ N → ƛ M ~ ƛ N
    compat-· : Compatible₂ _~_ _·_
    compat-force : Compatible₁ _~_ force
    compat-delay : Compatible₁ _~_ delay
    compat-constr :
      ∀ {X i} {Ms Ns : List (X ⊢)} →
        Pointwise _~_ Ms Ns →
        constr i Ms ~ constr i Ns
    compat-case :
      ∀ {X} {M N : X ⊢} {Ms Ns} →
        M ~ N →
        Pointwise _~_ Ms Ns →
        case M Ms ~ case N Ns
    compat-con : ∀ {k X} → con {X} k ~ con {X} k
    compat-builtin : ∀ {X} {f} → builtin {X} f ~ builtin {X} f
    compat-error : ∀ {X} → error {X} ~ error {X}
```
