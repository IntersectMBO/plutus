---
title: Untyped.Relation.Binary.Core
layout: page
---

```
module Untyped.Relation.Binary.Core where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (Dec; yes; no; _×-dec_)
open import Untyped
open import VerifiedCompilation.UntypedViews
```

## Binary relations on untyped terms

```
Relation : Set₁
Relation = ∀{n} → n ⊢ → n ⊢ → Set

Relation* : Set₁
Relation* = ∀{n} → List (n ⊢) → List (n ⊢) → Set
```

## Pointwise

Variant of Data.List.Relation.Binary.Pointwise that works well for well-scoped
terms, which have an implicit scope parameter. The polarity annotation helps for
constructing relations using `Untyped.Relation.Binary.Modular`.

```
data Pointwise {n} (@++ R : Relation) : List (n ⊢) → List (n ⊢) → Set where
  []  :
    Pointwise R [] []

  _∷_ : ∀ {M N : n ⊢} {Ms Ns} →
    R M N →
    Pointwise R Ms Ns →
    Pointwise R (M ∷ Ms) (N ∷ Ns)
```


## Decidable relations

```
DecidableRel : Relation → Set
DecidableRel R = ∀ {n : ℕ} (M M' : n ⊢) → Dec (R M M')
```


```
pointwise? : ∀ {R : Relation} →
  DecidableRel R →
  ∀ {n} (Ms Ns : List (n ⊢)) →
  Dec (Pointwise R Ms Ns)
pointwise? R? [] []         = yes []
pointwise? R? (x ∷ xs) (y ∷ ys)
  with R? x y ×-dec pointwise? R? xs ys
... | yes (Rxy , Rxsys) = yes (Rxy ∷ Rxsys)
... | no ¬R = no λ {(R ∷ Rs ) → ¬R (R , Rs)}
pointwise? R? (_ ∷ _) []    = no λ ()
pointwise? R? [] (_ ∷ _)    = no λ ()
```
