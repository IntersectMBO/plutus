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
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error; Let_In_)
open import VerifiedCompilation.UntypedViews
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Fin using (Fin; suc)
import Data.Fin as Fin using (_≟_)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Agda.Builtin.Equality using (_≡_; refl)
```

## Relation

A variable is strict in a term, if at least one occurrence of the variable does not appear inside any `delay`, `lambda` or `case` branch,
with the exception of when a lambda forms a `Let_In_` structure.
The Haskell implementation is used by the UPLC inliner and the UPLC CSE optimizer.

This is a sound approximation. Completeness is undecidable.

```
private variable
  n : ℕ

infix 1 _∈↓_ _∈↓?_

data _∈↓_ (v : Fin n) : (n ⊢) → Set where
  var : v ∈↓ (` v)
  _·ₗ
    : {M N : n ⊢}
    → v ∈↓ M
    → v ∈↓ M · N
  ·ᵣ_
    : {M N : n ⊢}
    → v ∈↓ N
    → v ∈↓ M · N
  force
    : {M : n ⊢}
    → v ∈↓ M
    → v ∈↓ force M
  constr
    : {i : ℕ} {Ms : List (n ⊢)}
    → Any (v ∈↓_) Ms
    → v ∈↓ constr i Ms
  scrut
    : {M : n ⊢} {Ns : List (n ⊢)}
    → v ∈↓ M
    → v ∈↓ case M Ns
  let-in
    : {M : n ⊢} {N : suc n ⊢}
    → suc v ∈↓ N
    → v ∈↓ Let M In N
```

## Decision Procedure

```
_any-∈↓?_ : (v : Fin n) (Ms : List (n ⊢)) → Dec (Any (v ∈↓_) Ms)

_∈↓?_ : (v : Fin n) (M : n ⊢) → Dec (v ∈↓ M)
v ∈↓? M with (`? ⋯) M
... | yes (`! (match! v')) with v Fin.≟ v'
...   | yes refl = yes var
...   | no ¬refl = no λ { var → ¬refl refl } 
v ∈↓? M
  | no ¬matchVar with (Let? ⋯ In? ⋯) M
... | yes (Let! (match! rhs) In! (match! body)) with suc v ∈↓? body 
...   | yes p = yes (let-in p)
...   | no ¬p with v ∈↓? rhs
...     | yes q = yes (·ᵣ q)
...     | no ¬q = no λ
          { (·ᵣ x) → ¬q x
          ; (let-in x) → ¬p x
          }
v ∈↓? M
  | no ¬matchVar
  | no ¬matchLet with (⋯ ·? ⋯) M
... | yes (match! lhs ·! match! rhs) with v ∈↓? lhs | v ∈↓? rhs
...   | yes p | _     = yes (p ·ₗ)
...   | _     | yes q = yes (·ᵣ q)
...   | no ¬p | no ¬q = no λ
        { (x ·ₗ) → ¬p x
        ; (·ᵣ x) → ¬q x
        ; (let-in x) → ¬matchLet (Let! match! rhs In! match! _) 
        }
v ∈↓? M 
  | no ¬matchVar
  | no ¬matchLet 
  | no ¬matchApp with (force? ⋯) M
... | yes (force! (match! M')) with v ∈↓? M'
...   | yes p = yes (force p)
...   | no ¬p = no λ { (force x) → ¬p x }
v ∈↓? M
  | no ¬matchVar
  | no ¬matchLet 
  | no ¬matchApp
  | no ¬matchForce with (constr? ⋯ ⋯) M
... | yes (constr! _ (match! Ms)) with v any-∈↓? Ms
...   | yes p = yes (constr p)
...   | no ¬p = no λ { (constr x) → ¬p x }
v ∈↓? M
  | no ¬matchVar
  | no ¬matchLet 
  | no ¬matchApp
  | no ¬matchForce 
  | no ¬matchConstr with (case? ⋯ ⋯) M
... | yes (case! (match! M') _) with v ∈↓? M'
...   | yes p = yes (scrut p)
...   | no ¬p = no λ { (scrut x) → ¬p x }
v ∈↓? M
  | no ¬matchVar
  | no ¬matchLet 
  | no ¬matchApp
  | no ¬matchForce 
  | no ¬matchConstr 
  | no ¬matchScrut = no λ
    { var → ¬matchVar (`! (match! v))
    ; (x ·ₗ) → ¬matchApp (match! _ ·! match! _)
    ; (·ᵣ x) → ¬matchApp (match! _ ·! match! _)
    ; (force x) → ¬matchForce (force! (match! _))
    ; (constr x) → ¬matchConstr (constr! (match! _) (match! _))
    ; (scrut x) → ¬matchScrut (case! (match! _) (match! _))
    ; (let-in x) → ¬matchApp (match! (ƛ _) ·! match! _)
    }

-- We could just use `Data.List.Relation.Unary.Any.any?`, but unfortunately the
-- termination checker isn't very happy about that.
x any-∈↓? [] = no λ ()
x any-∈↓? (M ∷ Ms) with x ∈↓? M
... | yes p = yes (here p)
... | no ¬p with x any-∈↓? Ms
...   | yes ps = yes (there ps)
...   | no ¬ps = no λ { (here p) → ¬p p ; (there ps) → ¬ps ps }
```