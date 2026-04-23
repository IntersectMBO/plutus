---
title: Untyped.Relation.Core
layout: page
---

```
module Untyped.Relation.Binary.Core where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (Dec)
open import Untyped
```

## Binary relations on untyped terms

```
Relation : Set₁
Relation = ∀{X} → X ⊢ → X ⊢ → Set
```

## Pointwise

Variant of Data.List.Relation.Binary.Pointwise that works well for well-scoped
terms, which have an implicit scope parameter.

```
data Pointwise {X} (@++ R : X ⊢ → X ⊢ → Set) : List (X ⊢) → List (X ⊢) → Set where
  []  :
    Pointwise R [] []

  _∷_ : ∀ {M N : X ⊢} {Ms Ns} →
    R M N →
    Pointwise R Ms Ns →
    Pointwise R (M ∷ Ms) (N ∷ Ns)
```

## Decidable relations

```
DecidableRel : Relation → Set
DecidableRel R = ∀ {X : ℕ} (M M' : X ⊢) → Dec (R M M')
```

## Relation transformers

Relation transformers are relations parametrised by other relations, such that
the parameter may only be used in strictly positive positions. This is useful
for defining inductive relations modularly.

```
RelationT : Set₁
RelationT = @++ Relation → Relation
```
