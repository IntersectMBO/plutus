---
title: Untyped.Relation.Pointwise
layout: page
---

This is often useful for the subterms of `case` and `constr`. Variant of
Data.List.Relation.Binary.Pointwise that works well for well-scoped terms, which
have an implicit scope parameter.

```
module Untyped.Relation.Pointwise where

open import Untyped
open import Untyped.Relation.Core
open import Untyped.Relation.Properties
open import Data.List
```

```
data Pointwise {X} (@++ R : X ⊢ → X ⊢ → Set) : List (X ⊢) → List (X ⊢) → Set where
  []  :
    Pointwise R [] []
  _∷_ : ∀ {M N : X ⊢} {Ms Ns} →
    R M N →
    Pointwise R Ms Ns →
    Pointwise R (M ∷ Ms) (N ∷ Ns)

pointwise-refl : ∀ {X} {R : Relation} {Ms : List (X ⊢)} → Reflexive R → Pointwise R Ms Ms
pointwise-refl {Ms = []} R-refl = []
pointwise-refl {R = R} {Ms = M ∷ Ms} R-refl = R-refl ∷ pointwise-refl {R = R} R-refl
```
