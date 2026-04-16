---
title: Untyped.Relation.Properties
layout: page
---

```
module Untyped.Relation.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Maybe

open import Untyped
open import Untyped.Relation.Core
```

## Why not reuse these properties from agda-stdlib?

We can't reuse `Relation.Binary` from the standard library here because a
relation on terms needs to be aware of the ℕ index that we use for representing
the scope. `Relation.Binary.Indexed.Heterogeneous` on the other hand is a bit
too general because its definitions may have indices that differ (see e.g.
`Transitive`), which makes using it inconvenient to use because Agda cannot
always infer the indices.

## Standard properties on relations

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

_⊆_ : Relation → Relation → Set
R ⊆ S =
  ∀ {X} {M N : X ⊢}
  → R M N
  → S M N
```

## Properties with respect to functions on terms

Operations on terms can be abbreviated:

```
Transform : Set
Transform = ∀{X} → X ⊢ → X ⊢

Transform₂ : Set
Transform₂ = ∀{X} → X ⊢ → X ⊢ → X ⊢

Deterministicᵣ : Relation → Set
Deterministicᵣ R = ∀ {X} {M N N' : X ⊢} → R M N → R M N' → N ≡ N'

Deterministicₗ : Relation → Set
Deterministicₗ R = ∀ {X} {M M' N : X ⊢} → R M N → R M' N → M ≡ M'
```

A compatible function maps related inputs to related outputs:

```
Compatible : Relation → Transform → Set
Compatible _~_ f =
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
```

A function refines a relation when it maps an input to a related output. Another
way of viewing this is that the graph of the function (i.e. a set of pairs) is a
subset of the relation (when viewed as set of pairs).

```
-- TODO make M explicit arg
Refines : Transform → Relation → Set
Refines f R =
  ∀ {X} {M : X ⊢}
  → R M (f M)
```

A similar notion for partial functions:

```
Refines? : (∀ {X} → X ⊢ → Maybe (X ⊢)) → Relation → Set
Refines? f R =
  ∀ {X} (M : X ⊢) {M' : X ⊢}
  → f M ≡ just M'
  → R M M'

Refines?-⊆ :
  ∀ {f : ∀ {X} → X ⊢ → Maybe (X ⊢)} {R S : Relation}
  → R ⊆ S
  → Refines? f R
  → Refines? f S
Refines?-⊆ R⊆S ext-f-R M eq = R⊆S (ext-f-R M eq)
```
