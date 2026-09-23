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
      ∀ {n} {x : Fin n}
      → ` x  ~ ` x
    compat-ƛ :
      ∀ {n} {M N : suc n ⊢}
      → M ~ N
      → ƛ M ~ ƛ N
    compat-· :
      Compatible₂ _~_ _·_
    compat-force :
      Compatible _~_ force
    compat-delay :
      Compatible _~_ delay
    compat-constr :
      ∀ {n i} {Ms Ns : List (n ⊢)}
      → Pointwise _~_ Ms Ns
      → constr i Ms ~ constr i Ns
    compat-case :
      ∀ {n} {M N : n ⊢} {Ms Ns}
      → M ~ N
      → Pointwise _~_ Ms Ns
      → case M Ms ~ case N Ns
    compat-con :
      ∀ {k n}
      → con {n} k ~ con {n} k
    compat-builtin :
      ∀ {n} {f}
      → builtin {n} f ~ builtin {n} f
    compat-error :
      ∀ {n}
      → error {n} ~ error {n}
```
