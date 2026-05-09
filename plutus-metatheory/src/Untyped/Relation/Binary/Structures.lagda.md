---
title: Untyped.Relation.Binary.Structures
layout: page
---

```
module Untyped.Relation.Binary.Structures where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.List using (List)

open import Untyped
open import Untyped.Relation.Binary.Core public
open import Untyped.Relation.Binary.Properties public
```

## Equivalence relations

```
record Equivalence (_~_ : Relation) : Set where
  field
    ~-refl : Reflexive _~_
    ~-trans : Transitive _~_
    ~-sym : Symmetric _~_
```

## Term-compatible relations

```
record TermCompatible (_~_ : Relation) : Set where
  field
    compat-var :
      ∀ {X} {n : Fin X}
      → ` n  ~ ` n
    compat-ƛ :
      ∀ {X} {M N : suc X ⊢}
      → M ~ N
      → ƛ M ~ ƛ N
    compat-· :
      Compatible₂ _~_ _·_
    compat-force :
      Compatible _~_ force
    compat-delay :
      Compatible _~_ delay
    compat-constr :
      ∀ {X i} {Ms Ns : List (X ⊢)}
      → Pointwise _~_ Ms Ns
      → constr i Ms ~ constr i Ns
    compat-case :
      ∀ {X} {M N : X ⊢} {Ms Ns}
      → M ~ N
      → Pointwise _~_ Ms Ns
      → case M Ms ~ case N Ns
    compat-con :
      ∀ {k X}
      → con {X} k ~ con {X} k
    compat-builtin :
      ∀ {X} {f}
      → builtin {X} f ~ builtin {X} f
    compat-error :
      ∀ {X}
      → error {X} ~ error {X}
```
