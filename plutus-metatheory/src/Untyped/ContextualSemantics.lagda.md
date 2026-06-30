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
open import Data.Nat using (ℕ; suc; _+_; _<_; _≤_; _≤ᵇ_)
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

||_||ₐ : {X : n ⊢} → B X → ℕ
||_||ₐ (builtinB b) = 0 
||_||ₐ (appB b v) = 1 + || b ||
||_||ₐ (forceB b) = || b ||

||_||ᶠ : {X : n ⊢} → B X → ℕ
||_||ᶠ (builtinB b) = 0 
||_||ᶠ (appB b v) = || b ||
||_||ᶠ (forceB b) = 1 + || b ||

data A where
  builtinA
    : {t : Builtin}
    → (b : B {n} (builtin t))
    → A {n} b
  appA
    : {t₁ t₂ : n ⊢}
    → (b : B (t₁ · t₂))
    -- we may apply app a number of times equal to the number of term arguments it has
    → || b ||ₐ ≤ args♯ (signature (β b))
    -- check that the builtin is not fully saturated
    → || b || < args♯ (signature (β b)) + fv (signature (β b))
    → A {n} b
  forceA
    : {t : n ⊢}
    → (b : B (force t))
    -- a builtin may be forced the number of times equal to the number of type arguments it has
    → || b ||ᶠ ≤ fv (signature (β b))
    -- check that the builtin is not fully saturated
    → || b || < args♯ (signature (β b)) + fv (signature (β b))
    → A {n} b

βᴬ : {t : n ⊢} {b : B t} → A b → Builtin
βᴬ (builtinA b) = β b
βᴬ (appA b x x₁) = β b
βᴬ (forceA b x x₁) = β b

||_||ᴬ : {t : n ⊢} {b : B t} → A b → ℕ
||_||ᴬ (builtinA b) = || b ||
||_||ᴬ (appA b x x₁) = || b ||
||_||ᴬ (forceA b x x₁) = || b ||

||_||ᶠᴬ : {t : n ⊢} {b : B t} → A b → ℕ
||_||ᶠᴬ (builtinA b) = || b ||ᶠ
||_||ᶠᴬ (appA b x x₁) = || b ||ᶠ
||_||ᶠᴬ (forceA b x x₁) = || b ||ᶠ

-- this doesn't typecheck because i need to use the information
-- that a is a partial application in order to lookup the next argument;
-- that means that the x is always smaller than the total number of args
-- and i should know that from the fact that a is a partial application
nextᴬ
  : {n : ℕ} {t : n ⊢} {b : B t}
  → (a : A b)
  → Maybe (Sig.fv⋆ (signature (βᴬ a)) / Sig.fv♯ (signature (βᴬ a)) ⊢⋆)
nextᴬ a with || a ||ᴬ
... | 0 =
  if ( || a ||ᶠᴬ ≤ᵇ fv (signature (βᴬ a)) )
    then nothing
    else (just (List⁺.head (Sig.args (signature (βᴬ a)))))
... | x = just (Vec.lookup (List⁺.toVec (Sig.args (signature (βᴬ a)))) {! Fin.fromℕ x  !})

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