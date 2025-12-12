---
title: Untyped renaming and substitution
layout: page
---

```
module Untyped.RenamingSubstitution where
```

## Imports

```
open import Function using (id;_∘_)
open import Data.List using (List;_∷_;[])
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;trans;cong;cong₂)

open import Utils using (Maybe;nothing;just)
open import Untyped using (_⊢)
open _⊢
```

## Renaming

When manipulating terms with de Bruijn indices, special care has to be taken
with free variables. As an example, consider the term `3 · λ 4`, which has one
free variable that occurs twice. Now let us substitute for that variable the
expression `(λ 0) · 1`, which itself has one free variable. The result is `((λ
0) · 1) · λ ((λ 0) · 2)`. Note that substitution under the lambda required
renaming the free variable (`1` became `2`), this is also called shifting. Also
note that bound variables are not changed (`0` stayed `0`).

A renaming is a function from de Bruijn indices to de Bruijn indices:

```
Ren : Set → Set → Set
Ren X Y = X → Y
```

For example, `just : Ren ⊥ (Maybe ⊥)` is a renaming that renames a variable `i` to `suc
i`. And `id` is the identity renaming.

As we have seen in the substitution example, we are only interested in renaming
free variables. So when renaming under a lambda abstraction:
- we need to take care not to rename `0`, which was bound by that lambda.
- the renaming function needs to be shifted: if it mapped `1` to `4`, under the
  lambda it will have to map `2` to `5`.

The `lift` function takes care of both:

```
lift : {X Y : Set} → Ren X Y → Ren (Maybe X) (Maybe Y)
lift ρ nothing = nothing
lift ρ (just x) = just (ρ x)

renList  : {X Y : Set} → Ren X Y → List (X ⊢) → List (Y ⊢)
ren : {X Y : Set} → Ren X Y → X ⊢ → Y ⊢
ren ρ (` x)         = ` (ρ x)
ren ρ (ƛ t)         = ƛ (ren (lift ρ) t)
ren ρ (t · u)       = ren ρ t · ren ρ u
ren ρ (force t)     = force (ren ρ t)
ren ρ (delay t)     = delay (ren ρ t)
ren ρ (con tcn)     = con tcn
ren ρ (builtin b)   = builtin b
ren ρ error         = error
ren ρ (constr i xs) = constr i (renList ρ xs)
ren ρ (case x ts)   = case (ren ρ x) (renList ρ ts)

renList ρ [] = []
renList ρ (x ∷ xs) = ren ρ x ∷ renList ρ xs

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

renList-cong : ∀{X Y}
    {ρ ρ' : Ren X Y}
  → (∀ x → ρ x ≡ ρ' x)
  → (t : List (X ⊢))
  → renList ρ t ≡ renList ρ' t

ren-cong : ∀{X Y}
    {ρ ρ' : Ren X Y}
  → (∀ x → ρ x ≡ ρ' x)
  → (t : X ⊢)
  → ren ρ t ≡ ren ρ' t
ren-cong p (` x)         = cong ` (p x)
ren-cong p (ƛ t)         = cong ƛ (ren-cong (lift-cong p) t)
ren-cong p (t · u)       = cong₂ _·_ (ren-cong p t) (ren-cong p u)
ren-cong p (force t)     = cong force (ren-cong p t)
ren-cong p (delay t)     = cong delay (ren-cong p t)
ren-cong p (con c)       = refl
ren-cong p (builtin b)   = refl
ren-cong p error         = refl
ren-cong p (constr i xs) = cong (constr i) (renList-cong p xs)
ren-cong p (case t ts)   = cong₂ case (ren-cong p t) (renList-cong p ts)

renList-cong p [] = refl
renList-cong p (x ∷ xs) = cong₂ _∷_ (ren-cong p x) (renList-cong p xs)

lift-id : ∀{X}(x : Maybe X) → id x ≡ lift id x
lift-id nothing  = refl
lift-id (just x) = refl

lift-comp : ∀{X Y Z}(g : Ren X Y)(f : Ren Y Z)(x : Maybe X)
  → lift (f ∘ g) x ≡ lift f (lift g x)
lift-comp g f nothing  = refl
lift-comp g f (just x) = refl

renList-id : ∀{X}(ts : List (X ⊢)) → ts ≡ renList id ts
ren-id : ∀{X}(t : X ⊢) → t ≡ ren id t
ren-id (` x)         = refl
ren-id (ƛ t)         = cong ƛ (trans (ren-id t) (ren-cong lift-id t))
ren-id (t · u)       = cong₂ _·_ (ren-id t) (ren-id u)
ren-id (force t)     = cong force (ren-id t)
ren-id (delay t)     = cong delay (ren-id t)
ren-id (con c)       = refl
ren-id (builtin b)   = refl
ren-id error         = refl
ren-id (constr i xs) = cong (constr i) (renList-id xs)
ren-id (case t ts)   = cong₂ case (ren-id t) (renList-id ts)

renList-id [] = refl
renList-id (x ∷ ts) = cong₂ _∷_ (ren-id x) (renList-id ts)


renList-comp : ∀{X Y Z}(g : Ren X Y)(f : Ren Y Z)(t : List (X ⊢))
  → renList (f ∘ g) t ≡ renList f (renList g t)
ren-comp : ∀{X Y Z}(g : Ren X Y)(f : Ren Y Z)(t : X ⊢)
  → ren (f ∘ g) t ≡ ren f (ren g t)
ren-comp ρ ρ' (` x)            = refl
ren-comp ρ ρ' (ƛ t)            = cong ƛ (trans
  (ren-cong (lift-comp ρ ρ') t)
  (ren-comp (lift ρ) (lift ρ') t))
ren-comp ρ ρ' (t · u)      = cong₂ _·_ (ren-comp ρ ρ' t) (ren-comp ρ ρ' u)
ren-comp ρ ρ' (force t)    = cong force (ren-comp ρ ρ' t)
ren-comp ρ ρ' (delay t)    = cong delay (ren-comp ρ ρ' t)
ren-comp ρ ρ' (con c)      = refl
ren-comp ρ ρ' (builtin b)  = refl
ren-comp ρ ρ' error        = refl
ren-comp ρ ρ' (constr i xs) = cong (constr i) (renList-comp ρ ρ' xs)
ren-comp ρ ρ' (case t ts)   = cong₂ case (ren-comp ρ ρ' t) (renList-comp ρ ρ' ts)

renList-comp ρ ρ' [] = refl
renList-comp ρ ρ' (x ∷ xs) = cong₂ _∷_ (ren-comp ρ ρ' x) (renList-comp ρ ρ' xs)
```

## Substitution

```
Sub : Set → Set → Set
Sub X Y = X → Y ⊢

lifts : {X Y : Set} → Sub X Y → Sub (Maybe X) (Maybe Y)
lifts ρ nothing = ` nothing
lifts ρ (just x) = ren just (ρ x)

subList : {X Y : Set} → Sub X Y → List (X ⊢) → List (Y ⊢)
sub : {X Y : Set} → Sub X Y → X ⊢ → Y ⊢
sub σ (` x)         = σ x
sub σ (ƛ t)         = ƛ (sub (lifts σ) t)
sub σ (t · u)       = sub σ t · sub σ u
sub σ (force t)     = force (sub σ t)
sub σ (delay t)     = delay (sub σ t)
sub σ (con tcn)     = con tcn
sub σ (builtin b)   = builtin b
sub σ error         = error
sub σ (constr i xs) = constr i (subList σ xs)
sub σ (case x ts)  = case (sub σ x) (subList σ ts)

subList σ [] = []
subList σ (x ∷ xs) = sub σ x ∷ subList σ xs

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

subList-cong : ∀{X Y}{σ σ' : Sub X Y}
  → (∀ x → σ x ≡ σ' x)
  → (ts : List (X ⊢))
  → subList σ ts ≡ subList σ' ts
sub-cong : ∀{X Y}{σ σ' : Sub X Y}
  → (∀ x → σ x ≡ σ' x)
  → (t : X ⊢)
  → sub σ t ≡ sub σ' t
sub-cong p (` x)         = p x
sub-cong p (ƛ t)         = cong ƛ (sub-cong (lifts-cong p) t)
sub-cong p (t · u)       = cong₂ _·_ (sub-cong p t) (sub-cong p u)
sub-cong p (force t)     = cong force (sub-cong p t)
sub-cong p (delay t)     = cong delay (sub-cong p t)
sub-cong p (con c)       = refl
sub-cong p (builtin b)   = refl
sub-cong p error         = refl
sub-cong p (constr i xs) = cong (constr i) (subList-cong p xs)
sub-cong p (case t ts)   = cong₂ case (sub-cong p t) (subList-cong p ts)

subList-cong p [] = refl
subList-cong p (x ∷ xs) = cong₂ _∷_ (sub-cong p x) (subList-cong p xs)

lifts-id : ∀{X}(x : Maybe X) → ` x ≡ lifts ` x
lifts-id nothing  = refl
lifts-id (just x) = refl

subList-id : ∀{X}(ts : List (X ⊢)) → ts ≡ subList ` ts
sub-id : ∀{X}(t : X ⊢) → t ≡ sub ` t
sub-id (` x)         = refl
sub-id (ƛ t)         = cong ƛ (trans (sub-id t) (sub-cong lifts-id t))
sub-id (t · u)       = cong₂ _·_ (sub-id t) (sub-id u)
sub-id (force t)     = cong force (sub-id t)
sub-id (delay t)     = cong delay (sub-id t)
sub-id (con c)       = refl
sub-id (builtin b)   = refl
sub-id error         = refl
sub-id (constr i xs) = cong (constr i) (subList-id xs)
sub-id (case t ts)   = cong₂ case (sub-id t) (subList-id ts)

subList-id [] = refl
subList-id (x ∷ xs) = cong₂ _∷_ (sub-id x) (subList-id xs)

lifts-lift : ∀{X Y Z}(g : Ren X Y)(f : Sub Y Z)(x : Maybe X)
  → lifts (f ∘ g) x ≡ lifts f (lift g x)
lifts-lift g f nothing  = refl
lifts-lift g f (just x) = refl

subList-ren : ∀{X Y Z}(ρ : Ren X Y)(σ : Sub Y Z)(xs : List (X ⊢))
            → subList (σ ∘ ρ) xs ≡ subList σ (renList ρ xs)
sub-ren : ∀{X Y Z}(ρ : Ren X Y)(σ : Sub Y Z)(t : X ⊢)
  → sub (σ ∘ ρ) t ≡ sub σ (ren ρ t)
sub-ren ρ σ (` x)         = refl
sub-ren ρ σ (ƛ t)         = cong ƛ (trans
  (sub-cong (lifts-lift ρ σ) t)
  (sub-ren (lift ρ) (lifts σ) t))
sub-ren ρ σ (t · u)       = cong₂ _·_ (sub-ren ρ σ t) (sub-ren ρ σ u)
sub-ren ρ σ (force t)     = cong force (sub-ren ρ σ t)
sub-ren ρ σ (delay t)     = cong delay (sub-ren ρ σ t)
sub-ren ρ σ (con c)       = refl
sub-ren ρ σ (builtin b)   = refl
sub-ren ρ σ error         = refl
sub-ren ρ σ (constr i xs) = cong (constr i) (subList-ren ρ σ xs)
sub-ren ρ σ (case t ts)   = cong₂ case (sub-ren ρ σ t) (subList-ren ρ σ ts)

subList-ren ρ σ [] = refl
subList-ren ρ σ (x ∷ xs) = cong₂ _∷_ (sub-ren ρ σ x) (subList-ren ρ σ xs)

ren-lift-lifts : ∀{X Y Z}(g : Sub X Y)(f : Ren Y Z)(x : Maybe X)
  → lifts (ren f ∘ g) x ≡ ren (lift f) (lifts g x)
ren-lift-lifts g f nothing  = refl
ren-lift-lifts g f (just x) = trans
  (sym (ren-comp f just (g x)))
  (ren-comp just (lift f) (g x))

renList-sub : ∀{X Y Z}(σ : Sub X Y)(ρ : Ren Y Z)(xs : List (X ⊢))
            → subList (ren ρ ∘ σ) xs ≡ renList ρ (subList σ xs)
ren-sub : ∀{X Y Z}(σ : Sub X Y)(ρ : Ren Y Z)(t : X ⊢)
  → sub (ren ρ ∘ σ) t ≡ ren ρ (sub σ t)
ren-sub σ ρ (` x)         = refl
ren-sub σ ρ (ƛ t)         = cong ƛ (trans
  (sub-cong (ren-lift-lifts σ ρ) t)
  (ren-sub (lifts σ) (lift ρ) t))
ren-sub σ ρ (t · u)       = cong₂ _·_ (ren-sub σ ρ t) (ren-sub σ ρ u)
ren-sub σ ρ (force t)     = cong force (ren-sub σ ρ t)
ren-sub σ ρ (delay t)     = cong delay (ren-sub σ ρ t)
ren-sub σ ρ (con c)       = refl
ren-sub σ ρ (builtin b)   = refl
ren-sub σ ρ error         = refl
ren-sub σ ρ (constr i xs) = cong (constr i) (renList-sub σ ρ xs)
ren-sub σ ρ (case t ts)   = cong₂ case (ren-sub σ ρ t) (renList-sub σ ρ ts)

renList-sub σ ρ [] = refl
renList-sub σ ρ (x ∷ xs) = cong₂ _∷_ (ren-sub σ ρ x) (renList-sub σ ρ xs)

lifts-comp : ∀{X Y Z}(g : Sub X Y)(f : Sub Y Z)(x : Maybe X)
  → lifts (sub f ∘ g) x ≡ sub (lifts f) (lifts g x)
lifts-comp g f nothing  = refl
lifts-comp g f (just x) = trans
  (sym (ren-sub f just (g x)))
  (sub-ren just (lifts f) (g x))


subList-comp : ∀{X Y Z}(g : Sub X Y)(f : Sub Y Z)(xs : List (X ⊢))
             → subList (sub f ∘ g) xs ≡ subList f (subList g xs)
sub-comp : ∀{X Y Z}(g : Sub X Y)(f : Sub Y Z)(t : X ⊢)
  → sub (sub f ∘ g) t ≡ sub f (sub g t)
sub-comp g f (` x)       = refl
sub-comp g f (ƛ t)       =
  cong ƛ (trans (sub-cong (lifts-comp g f) t) (sub-comp (lifts g) (lifts f) t))
sub-comp g f (t · u)       = cong₂ _·_ (sub-comp g f t) (sub-comp g f u)
sub-comp g f (force t)     = cong force (sub-comp g f t)
sub-comp g f (delay t)     = cong delay (sub-comp g f t)
sub-comp g f (con c)       = refl
sub-comp g f (builtin b)   = refl
sub-comp g f error         = refl
sub-comp g f (constr i xs) = cong (constr i) (subList-comp g f xs)
sub-comp g f (case t ts)   = cong₂ case (sub-comp g f t) (subList-comp g f ts)

subList-comp g f [] = refl
subList-comp g f (x ∷ xs) = cong₂ _∷_ (sub-comp g f x) (subList-comp g f xs)
```
