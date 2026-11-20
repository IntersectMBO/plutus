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
  M N L : n ⊢

-- TODO: merge A and PAB?
-- PAB : partially (value) applied builtins
data PAB : n ⊢ → Set 
data Value : n ⊢ → Set
ArgTy : PAB M → Set
data A : (pab : PAB M) → ℕ → NE.List⁺ (ArgTy pab) → Set 

variable
  fl : ℕ 
  pab : PAB M

data PAB where
  builtin
    : (b : Builtin)
    → PAB {n} (builtin b)
  _·_
    : PAB M
    → Value N
    → PAB (M · N)
  force
    : PAB M
    → PAB (force M)

-- the signature of the builtin underlying the spine 'b'
β : PAB M → Builtin
β (builtin b) = b
β (pab · v) = β pab
β (force pab) = β pab

-- the type of a term argument expected by the 'b' builtin
sigOf : PAB M → Sig
sigOf pab = signature (β pab)

||_|| : PAB M → ℕ
||_|| (builtin b) = 0 
||_|| (pab · v) = 1 + || pab ||
||_|| (force pab) = 1 + || pab ||

ArgTy pab = Sig.fv⋆ (sigOf pab) / Sig.fv♯ (sigOf pab) ⊢⋆

data A where
  builtin
    : (b : Builtin)
    → A (builtin {n} b) (fv (signature b)) (Sig.args (signature b))
  force
    -- a force is still expected: consume it, leaving the argument list suffix untouched
    : {al : NE.List⁺ (ArgTy pab)}
    → A pab (suc fl) al
    → A (force pab) fl al
  _·_
    : {τ : ArgTy pab}
      {as : NE.List⁺ (ArgTy pab)}
    -- all forces done: consume the head argument τ, non-empty suffix 'as' remains
    → A pab zero (τ NE.∷⁺ as)
    → (v : Value N)
    → A (pab · v) zero as

βᴬ : {al : NE.List⁺ (ArgTy pab)} → A pab fl al → Builtin
βᴬ {pab = pab} _ = β pab

-- number of forces performed so far: total type variables minus those still expected
||_||ᶠᴬ
  : {al : NE.List⁺ (ArgTy pab)}
  → A pab fl al
  → ℕ
||_||ᶠᴬ {pab = pab} {fl = fl} _ = fv (sigOf pab) ∸ fl

-- number of forces + applications performed so far
||_||ᴬ
  : {pab : PAB M} {fl : ℕ} {al : NE.List⁺ (ArgTy pab)}
  → A pab fl al
  → ℕ
||_||ᴬ {pab = pab} {fl = fl} {al = al} a =
  || a ||ᶠᴬ + (args♯ (sigOf pab) ∸ NE.length al)

-- The type of the next argument the partial application expects:
--   - nothing if the next expected argument is a type argument (a force)
--   - just τ if the next expected argument is a term argument of type τ
nextᴬ
  : {pab : PAB M} {fl : ℕ} {al : NE.List⁺ (ArgTy pab)}
  → A pab fl al
  → Maybe (ArgTy pab)
nextᴬ {fl = suc _} _ = nothing
nextᴬ {fl = zero} {al = al} _ = just (NE.head al)

-- TODO: rename t's to M's
data Value where
  conᵥ : (t : TmCon) → Value {n} (con t)
  delayᵥ : (t : n ⊢) → Value (delay t)
  ƛᵥ : (t : suc n ⊢) → Value (ƛ t)
  constrᵥ : (i : ℕ) (ts : List (n ⊢)) → All Value ts → Value (constr i ts)
  bAppᵥ
    : {al : NE.List⁺ (ArgTy pab)}
    → A pab fl al
    → Value M

variable
  al : {pab : PAB M} → NE.List⁺ (ArgTy pab)

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
  -- caseconstr
  --   : {i l : ℕ} {vs ts : List (n ⊢)} {f : n ⊢} 
  --   → All Value vs
  --   -- TODO: lookup i in ts, we need to deal with empty ts's and index out of bounds
  --   → (case (constr i vs) ts) ⟶ (multiApp {!   !} vs)


```