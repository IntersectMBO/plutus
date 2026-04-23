---
title: Untyped.Relation.Binary.Properties
layout: page
---

```
module Untyped.Relation.Binary.Properties where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Product

open import Untyped
open import Untyped.Relation.Binary.Core
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

⊆-trans :
  {R S T : Relation}
  → R ⊆ S
  → S ⊆ T
  → R ⊆ T
⊆-trans R⊆S S⊆T RMN = S⊆T (R⊆S RMN)
```

## Properties with respect to functions on terms

Operations on terms can be abbreviated:

```
Transform : Set
Transform = ∀{X} → X ⊢ → X ⊢

Transform? : Set
Transform? = ∀{X} → X ⊢ → Maybe (X ⊢)

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

## Pointwise


```
pointwise-refl : ∀ {X} {R : Relation} {Ms : List (X ⊢)} → Reflexive R → Pointwise R Ms Ms
pointwise-refl {Ms = []} R-refl = []
pointwise-refl {R = R} {Ms = M ∷ Ms} R-refl = R-refl ∷ pointwise-refl {R = R} R-refl
```

## Refinement

A function refines a relation `R `when each input-output pair is related in R.

```
Refines : Transform → Relation → Set
Refines f R = ∀ {X} {M : X ⊢} → R M (f M)
```

There is a similar notion for partial functions:

```
Refines? : Transform? → Relation → Set
Refines? f R =
  ∀ {X}
  → (M N : X ⊢)
  → f M ≡ just N
  → R M N

Refines?-⊆ :
  ∀ {f : ∀ {X} → X ⊢ → Maybe (X ⊢)} {R S : Relation}
  → R ⊆ S
  → Refines? f R
  → Refines? f S
Refines?-⊆ R⊆S refines?-f _ _ eq = R⊆S (refines?-f _ _ eq)
```

A partial function can be a refinement by construction, if it also returns the
proof of inhabitance of the relation:

```
Refinement? : Relation → Set
Refinement? R =
  ∀ {X}
  → (M : X ⊢)
  → Maybe (∃ (λ M' → R M M'))

refine? : ∀ {X} {R : Relation} → Refinement? R → X ⊢ → Maybe (X ⊢)
refine? f M with f M
... | nothing = nothing
... | just (M' , _) = just M'

refine?-refines :
  ∀ {R : Relation}
  → (f : Refinement? R)
  → Refines? (refine? f) R
refine?-refines f M _ fM≡just with f M | fM≡just
... | just ( _ , RMN) | refl = RMN
```
