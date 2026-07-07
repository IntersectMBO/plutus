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
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _≤ᵇ_)
open import Data.List using (List; _++_)
import Data.List as List
open import Data.List.Relation.Unary.All using (All)
open import Builtin
open import Builtin.Signature using (_/_⊢⋆; args♯; Sig; fv)
open import Untyped.RenamingSubstitution using (_[_])
open import Data.Vec using (Vec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (if_then_else_)
import Data.List.NonEmpty as List⁺
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
β : {X : n ⊢} → B X → Builtin
-- the signature of the builtin underlying the spine 'b'
sigOf : {X : n ⊢} → B X → Sig
-- the type of a term argument expected by the 'b' builtin
ArgTy : {X : n ⊢} → B X → Set
data A : {X : n ⊢} → (b : B X) → ℕ → NE.List⁺ (ArgTy b) → Set

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

β (builtinB b) = b
β (appB b v) = β b
β (forceB b) = β b

sigOf b = signature (β b)

ArgTy b = Sig.fv⋆ (sigOf b) / Sig.fv♯ (sigOf b) ⊢⋆

||_|| : {X : n ⊢} → B X → ℕ
||_|| (builtinB b) = 0 
||_|| (appB b v) = 1 + || b ||
||_|| (forceB b) = 1 + || b ||

data A where
  builtinA
    : (b : Builtin)
    → A (builtinB {n} b) (fv (signature b)) (Sig.args (signature b))
  forceA
    : {t : n ⊢} {b : B t} {fl : ℕ}
      {al : NE.List⁺ (ArgTy b)}
    -- a force is still expected: consume it, leaving the argument list suffix untouched
    → A b (suc fl) al
    → A (forceB b) fl al
  appA
    : {t₁ t₂ : n ⊢} {b : B t₁}
      {τ : ArgTy b}
      {as : NE.List⁺ (ArgTy b)}
    -- all forces done: consume the head argument τ, non-empty suffix 'as' remains
    → A b zero (τ NE.∷⁺ as)
    → (v : Value t₂)
    → A (appB b v) zero as

βᴬ : {t : n ⊢} {b : B t} {fl : ℕ}
     {al : NE.List⁺ (ArgTy b)}
   → A b fl al → Builtin
βᴬ {b = b} _ = β b

-- number of forces performed so far: total type variables minus those still expected
||_||ᶠᴬ
  : {t : n ⊢} {b : B t} {fl : ℕ} {al : NE.List⁺ (ArgTy b)}
  → A b fl al
  → ℕ
||_||ᶠᴬ {b = b} {fl = fl} _ = fv (sigOf b) ∸ fl

-- number of forces + applications performed so far
||_||ᴬ
  : {t : n ⊢} {b : B t} {fl : ℕ} {al : NE.List⁺ (ArgTy b)}
  → A b fl al
  → ℕ
||_||ᴬ {b = b} {fl = fl} {al = al} a =
  || a ||ᶠᴬ + (args♯ (sigOf b) ∸ NE.length al)

-- The type of the next argument the partial application expects:
--   - nothing if the next expected argument is a type argument (a force)
--   - just τ if the next expected argument is a term argument of type τ
nextᴬ
  : {t : n ⊢} {b : B t} {fl : ℕ} {al : NE.List⁺ (ArgTy b)}
  → A b fl al
  → Maybe (ArgTy b)
nextᴬ {fl = suc _} _ = nothing
nextᴬ {fl = zero} {al = al} _ = just (NE.head al)

data Value where
  conᵥ : (t : TmCon) → Value {n} (con t)
  delayᵥ : (t : n ⊢) → Value (delay t)
  ƛᵥ : (t : suc n ⊢) → Value (ƛ t)
  constrᵥ : (i : ℕ) (ts : List (n ⊢)) → All Value ts → Value (constr i ts)
  bAppᵥ
    : {t : n ⊢} {b : B t} {fl : ℕ} {al : NE.List⁺ (ArgTy b)}
    → A b fl al
    → Value t

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