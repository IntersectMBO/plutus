---
title: Contextual Semantics
layout: page
---

```
module Untyped.ContextualSemantics where
```

## Imports

```
open import Untyped
open import Data.Nat using (ℕ; suc; _+_; _<_; _≤_)
open import Data.List using (List; _++_)
import Data.List as List
open import Data.List.Relation.Unary.All using (All)
open import Builtin
open import Builtin.Signature using (args♯; Sig)
open import Untyped.RenamingSubstitution using (_[_])
open import Data.Vec using (Vec)
import Data.List.NonEmpty as NE
import Data.Vec as Vec
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_)

```

## TODO

```
variable
  n : ℕ

data B : n ⊢ → Set 
data Value : n ⊢ → Set
data A : {X : n ⊢} → B X → Set

data B where
  builtinB
    : (b : Builtin)
    → B {n} (builtin b)
  appB
    : {t₁ t₂ : n ⊢}
    → B t₁
    → Value t₂
    → B (t₁ · t₂)
  forceB
    : {t : n ⊢}
    → B t
    → B (force t)

β : {X : n ⊢} → B X → Builtin 
β (builtinB b) = b
β (appB b v) = β b
β (forceB b) = β b

||_|| : {X : n ⊢} → B X → ℕ
||_|| (builtinB b) = 0 
||_|| (appB b v) = 1 + || b ||
||_|| (forceB b) = 1 + || b ||

data A where
  builtinA
    : {b : Builtin}
    → A {n} (builtinB b)
  appA
    : {t₁ t₂ : n ⊢} (b : B (t₁ · t₂))
    → || b || < args♯ (signature (β b))
    -- TODO: quantification?
    → A {n} b
  forceA
    : {t : n ⊢} (b : B (force t))
    → || b || < 1 -- TODO: we don't formalize quantifications, in practice I've only seen them applied directly to 'builtin b', but this should be fixed separately
    → A {n} b

data Value where
  conᵥ : (t : TmCon) → Value {n} (con t)
  delayᵥ : (t : n ⊢) → Value (delay t)
  ƛᵥ : (t : suc n ⊢) → Value (ƛ t)
  constrᵥ : (i : ℕ) (ts : List (n ⊢)) → All Value ts → Value (constr i ts)
  bAppᵥ : {t : n ⊢} {b : B t} → A b → Value t

data Frame : n ⊢ → Set where
  □
    : {t : n ⊢}
    → Frame t
  _ᶠ·_
    : {t₁ : n ⊢}
    → Frame t₁
    → (t₂ : n ⊢)
    → Frame (t₁ · t₂) 
  _·ᶠ_
    : {t₁ t₂ : n ⊢}
    → Value t₁
    → Frame t₂
    → Frame (t₁ · t₂)
  forceᶠ
    : {t : n ⊢}
    → Frame t
    → Frame (force t)
  constrᶠ
    : {f : n ⊢} {vs : List (n ⊢)}
    → (i : ℕ)
    → All Value vs
    → Frame f
    → (ts : List (n ⊢))
    → Frame (constr i (vs ++ List.[ f ] ++ ts))
  caseᶠ
    : {f : n ⊢}
    → Frame f
    → (ts : List (n ⊢))
    → Frame (case f ts)

-- TODO: implement
postulate
  multiApp : {t : n ⊢} → Value t → List (n ⊢) → n ⊢

-- TODO: rename constructors
data _⟶_ : n ⊢ → n ⊢ → Set where
  lamapp
    : {t₁ : suc n ⊢} {t₂ : n ⊢}
    → Value t₂
    → (ƛ t₁ · t₂) ⟶ (t₁ [ t₂ ])
  forcedelay
    : {t : n ⊢}
    → (force (delay t)) ⟶ t
  caseconstr
    : {i l : ℕ} {vs ts : List (n ⊢)} {f : n ⊢} 
    → All Value vs
    -- TODO: lookup i in ts, we need to deal with empty ts's and index out of bounds
    → (case (constr i vs) ts) ⟶ (multiApp {!   !} vs)


```