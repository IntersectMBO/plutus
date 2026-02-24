---
title: Untyped.Strictness
layout: page
---

# Whether a variable is strict in the given term
```
module Untyped.Strictness where

```
## Imports

```
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Fin using (Fin)
import Data.Fin as Fin using (_≟_)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Agda.Builtin.Equality using (_≡_; refl)
```

## Relation

A variable is strict in a term, if at least one occurrence of the variable does not appear inside any `delay`, `lambda` or `case` branch.
The Haskell implementation is used by the UPLC inliner.

This is a sound approximation. Completeness is undecidable.

```
infix 1 _∈↓_ _∈↓?_

data _∈↓_ {X : ℕ} (x : Fin X) : (X ⊢) → Set where
  var : x ∈↓ (` x)
  _·ₗ : {M N : X ⊢} → x ∈↓ M → x ∈↓ M · N
  ·ᵣ_ : {M N : X ⊢} → x ∈↓ N → x ∈↓ M · N
  force : {M : X ⊢}   → x ∈↓ M  → x ∈↓ force M
  constr : {i : ℕ} {Ms : List (X ⊢)} → Any (x ∈↓_) Ms → x ∈↓ constr i Ms
  scrut : {M : X ⊢} {Ns : List (X ⊢)} → x ∈↓ M → x ∈↓ case M Ns
```

## Decision Procedure

```
_any-∈↓?_ : {X : ℕ} (x : Fin X) (Ms : List (X ⊢)) → Dec (Any (x ∈↓_) Ms)

_∈↓?_ : {X : ℕ} (x : Fin X) (M : X ⊢) → Dec (x ∈↓ M)
x ∈↓? ` x′ with x Fin.≟ x′
... | yes refl = yes var
... | no x≢x′ = no λ { var → x≢x′ refl }
x ∈↓? M · N with x ∈↓? M | x ∈↓? N
... | yes l | _ = yes (l ·ₗ)
... | no _ | yes r = yes (·ᵣ r)
... | no ¬l | no ¬r = no λ { (l ·ₗ) → ¬l l ; (·ᵣ r) → ¬r r }
x ∈↓? force M with x ∈↓? M
... | yes p  = yes (force p)
... | no  ¬p = no λ { (force p) → ¬p p }
x ∈↓? constr i [] = no λ { (constr ()) }
x ∈↓? constr i Ms@(_ ∷ _) with x any-∈↓? Ms
... | yes ps = yes (constr ps)
... | no ¬ps = no λ { (constr ps) → ¬ps ps }
x ∈↓? case M Ns with x ∈↓? M
... | yes p = yes (scrut p)
... | no ¬p = no λ { (scrut p) → ¬p p }
x ∈↓? ƛ M = no λ ()
x ∈↓? delay t = no λ ()
x ∈↓? con c = no λ ()
x ∈↓? builtin b = no λ ()
x ∈↓? error = no λ ()

-- We could just use `Data.List.Relation.Unary.Any.any?`, but unfortunately the
-- termination checker isn't very happy about that.
x any-∈↓? [] = no λ ()
x any-∈↓? (M ∷ Ms) with x ∈↓? M
... | yes p = yes (here p)
... | no ¬p with x any-∈↓? Ms
...   | yes ps = yes (there ps)
...   | no ¬ps = no λ { (here p) → ¬p p ; (there ps) → ¬ps ps }
```