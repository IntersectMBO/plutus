---
title: Untyped renaming and substitution
layout: page
---

```
module Untyped.RenamingSubstitution where
```

## Imports

```
open import Untyped

open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Function
open import Utils
```

## Renaming



```
Ren : Set → Set → Set
Ren X Y = X → Y

lift : {X Y : Set} → Ren X Y → Ren (Maybe X) (Maybe Y)
lift ρ nothing = nothing
lift ρ (just x) = just (ρ x)

ren : {X Y : Set} → Ren X Y → X ⊢ → Y ⊢
ren ρ (` x)       = ` (ρ x)
ren ρ (ƛ t)       = ƛ (ren (lift ρ) t)
ren ρ (t · u)     = ren ρ t · ren ρ u
ren ρ (force t)   = force (ren ρ t)
ren ρ (delay t)   = delay (ren ρ t)
ren ρ (con tcn)   = con tcn
ren ρ (builtin b) = builtin b
ren ρ error       = error

weaken : {X : Set} → X ⊢ → Maybe X ⊢
weaken t = ren just t
```

Proofs that renaming forms a functor

```
lift-cong : ∀{X Y}
    {ρ ρ' : Ren X Y}
  → (∀ x → ρ x ≡ ρ' x)
  → (x : Maybe X)
    --------------------
  → lift ρ x ≡ lift ρ' x
lift-cong p nothing  = refl
lift-cong p (just x) = cong just (p x)

ren-cong : ∀{X Y}
    {ρ ρ' : Ren X Y}
  → (∀ x → ρ x ≡ ρ' x)
  → (t : X ⊢)
  → ren ρ t ≡ ren ρ' t
ren-cong p (` x)       = cong ` (p x)
ren-cong p (ƛ t)       = cong ƛ (ren-cong (lift-cong p) t)
ren-cong p (t · u)     = cong₂ _·_ (ren-cong p t) (ren-cong p u)
ren-cong p (force t)   = cong force (ren-cong p t)
ren-cong p (delay t)   = cong delay (ren-cong p t)
ren-cong p (con c)     = refl
ren-cong p (builtin b) = refl
ren-cong p error       = refl

lift-id : ∀{X}(x : Maybe X) → id x ≡ lift id x
lift-id nothing  = refl
lift-id (just x) = refl

lift-comp : ∀{X Y Z}(g : Ren X Y)(f : Ren Y Z)(x : Maybe X)
  → lift (f ∘ g) x ≡ lift f (lift g x)
lift-comp g f nothing  = refl
lift-comp g f (just x) = refl

ren-id : ∀{X}(t : X ⊢) → t ≡ ren id t
ren-id (` x)       = refl
ren-id (ƛ t)       = cong ƛ (trans (ren-id t) (ren-cong lift-id t)) 
ren-id (t · u)     = cong₂ _·_ (ren-id t) (ren-id u)
ren-id (force t)   = cong force (ren-id t)
ren-id (delay t)   = cong delay (ren-id t) 
ren-id (con c)     = refl
ren-id (builtin b) = refl
ren-id error       = refl

ren-comp : ∀{X Y Z}(g : Ren X Y)(f : Ren Y Z)(t : X ⊢)
  → ren (f ∘ g) t ≡ ren f (ren g t)
ren-comp ρ ρ' (` x)            = refl
ren-comp ρ ρ' (ƛ t)            = cong ƛ (trans
  (ren-cong (lift-comp ρ ρ') t)
  (ren-comp (lift ρ) (lift ρ') t))
ren-comp ρ ρ' (t · u)     = cong₂ _·_ (ren-comp ρ ρ' t) (ren-comp ρ ρ' u)
ren-comp ρ ρ' (force t)   = cong force (ren-comp ρ ρ' t)
ren-comp ρ ρ' (delay t)   = cong delay (ren-comp ρ ρ' t)
ren-comp ρ ρ' (con c)     = refl
ren-comp ρ ρ' (builtin b) = refl
ren-comp ρ ρ' error       = refl
```

## Substitution

```
Sub : Set → Set → Set
Sub X Y = X → Y ⊢

lifts : {X Y : Set} → Sub X Y → Sub (Maybe X) (Maybe Y)
lifts ρ nothing = ` nothing
lifts ρ (just x) = ren just (ρ x)

sub : {X Y : Set} → Sub X Y → X ⊢ → Y ⊢
sub σ (` x)       = σ x
sub σ (ƛ t)       = ƛ (sub (lifts σ) t) 
sub σ (t · u)     = sub σ t · sub σ u
sub σ (force t)   = force (sub σ t)
sub σ (delay t)   = delay (sub σ t)
sub σ (con tcn)   = con tcn
sub σ (builtin b) = builtin b
sub σ error       = error

extend : ∀{X Y} → Sub X Y → Y ⊢ → Sub (Maybe X) Y
extend σ t nothing  = t
extend σ t (just x) = σ x

_[_] : ∀{X} → Maybe X ⊢ → X ⊢ → X ⊢
t [ u ] = sub (extend ` u) t
```

Proofs that substitution forms a monad

```
lifts-cong : ∀{X Y}{σ σ' : Sub X Y}
  → (∀ x → σ x ≡ σ' x)
  → (x : Maybe X)
  → lifts σ x ≡ lifts σ' x
lifts-cong p nothing  = refl
lifts-cong p (just x) = cong (ren just) (p x) 

sub-cong : ∀{X Y}{σ σ' : Sub X Y}
  → (∀ x → σ x ≡ σ' x)
  → (t : X ⊢)
  → sub σ t ≡ sub σ' t

sub-cong p (` x)       = p x
sub-cong p (ƛ t)       = cong ƛ (sub-cong (lifts-cong p) t)
sub-cong p (t · u)     = cong₂ _·_ (sub-cong p t) (sub-cong p u)
sub-cong p (force t)   = cong force (sub-cong p t)
sub-cong p (delay t)   = cong delay (sub-cong p t)
sub-cong p (con c)     = refl
sub-cong p (builtin b) = refl
sub-cong p error       = refl

lifts-id : ∀{X}(x : Maybe X) → ` x ≡ lifts ` x
lifts-id nothing  = refl
lifts-id (just x) = refl

sub-id : ∀{X}(t : X ⊢) → t ≡ sub ` t
sub-id (` x)       = refl
sub-id (ƛ t)       = cong ƛ (trans (sub-id t) (sub-cong lifts-id t))
sub-id (t · u)     = cong₂ _·_ (sub-id t) (sub-id u)
sub-id (force t)   = cong force (sub-id t)
sub-id (delay t)   = cong delay (sub-id t)
sub-id (con c)     = refl
sub-id (builtin b) = refl
sub-id error       = refl

lifts-lift : ∀{X Y Z}(g : Ren X Y)(f : Sub Y Z)(x : Maybe X)
  → lifts (f ∘ g) x ≡ lifts f (lift g x)
lifts-lift g f nothing  = refl
lifts-lift g f (just x) = refl

sub-ren : ∀{X Y Z}(ρ : Ren X Y)(σ : Sub Y Z)(t : X ⊢)
  → sub (σ ∘ ρ) t ≡ sub σ (ren ρ t)
sub-ren ρ σ (` x)       = refl
sub-ren ρ σ (ƛ t)       = cong ƛ (trans
  (sub-cong (lifts-lift ρ σ) t)
  (sub-ren (lift ρ) (lifts σ) t))
sub-ren ρ σ (t · u)     = cong₂ _·_ (sub-ren ρ σ t) (sub-ren ρ σ u) 
sub-ren ρ σ (force t)   = cong force (sub-ren ρ σ t)
sub-ren ρ σ (delay t)   = cong delay (sub-ren ρ σ t)
sub-ren ρ σ (con c)     = refl
sub-ren ρ σ (builtin b) = refl
sub-ren ρ σ error       = refl

ren-lift-lifts : ∀{X Y Z}(g : Sub X Y)(f : Ren Y Z)(x : Maybe X)
  → lifts (ren f ∘ g) x ≡ ren (lift f) (lifts g x)
ren-lift-lifts g f nothing  = refl
ren-lift-lifts g f (just x) = trans
  (sym (ren-comp f just (g x)))
  (ren-comp just (lift f) (g x))

ren-sub : ∀{X Y Z}(σ : Sub X Y)(ρ : Ren Y Z)(t : X ⊢)
  → sub (ren ρ ∘ σ) t ≡ ren ρ (sub σ t)
ren-sub σ ρ (` x)               = refl
ren-sub σ ρ (ƛ t)               = cong ƛ (trans
  (sub-cong (ren-lift-lifts σ ρ) t)
  (ren-sub (lifts σ) (lift ρ) t))
ren-sub σ ρ (t · u)     = cong₂ _·_ (ren-sub σ ρ t) (ren-sub σ ρ u) 
ren-sub σ ρ (force t)   = cong force (ren-sub σ ρ t)
ren-sub σ ρ (delay t)   = cong delay (ren-sub σ ρ t)
ren-sub σ ρ (con c)     = refl
ren-sub σ ρ (builtin b) = refl
ren-sub σ ρ error       = refl

lifts-comp : ∀{X Y Z}(g : Sub X Y)(f : Sub Y Z)(x : Maybe X)
  → lifts (sub f ∘ g) x ≡ sub (lifts f) (lifts g x)
lifts-comp g f nothing  = refl
lifts-comp g f (just x) = trans
  (sym (ren-sub f just (g x)))
  (sub-ren just (lifts f) (g x))

sub-comp : ∀{X Y Z}(g : Sub X Y)(f : Sub Y Z)(t : X ⊢)
  → sub (sub f ∘ g) t ≡ sub f (sub g t)
sub-comp g f (` x)       = refl
sub-comp g f (ƛ t)       =
  cong ƛ (trans (sub-cong (lifts-comp g f) t) (sub-comp (lifts g) (lifts f) t))
sub-comp g f (t · u)     = cong₂ _·_ (sub-comp g f t) (sub-comp g f u)
sub-comp g f (force t)   = cong force (sub-comp g f t)
sub-comp g f (delay t)   = cong delay (sub-comp g f t)
sub-comp g f (con c)     = refl
sub-comp g f (builtin b) = refl
sub-comp g f error       = refl
```
