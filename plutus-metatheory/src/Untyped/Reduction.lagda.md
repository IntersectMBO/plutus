---
title: Untyped Reductions
layout: page
---

```
module Untyped.Reduction where
```

## Imports

```
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Untyped.RenamingSubstitution using (_[_])
open import Data.Maybe using (Maybe; just; nothing)
open import RawU using (TmCon)
open import Builtin using (Builtin;equals;decBuiltin)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Negation using (contradiction)
```
## Values
```

data Value {X : Set} : X ⊢ → Set where
  delay : { a : X ⊢} → Value (delay a)
  ƛ : { a : (Maybe X) ⊢ } → Value (ƛ a)
  con : {n : TmCon} → Value (con n)
  builtin : {b : Builtin} → Value (builtin b)
-- constr ??? - when all of its arguments are values
  error : Value error

```
## Reduction Steps
```

infix 5 _⟶_
data _⟶_ {X : Set} : X ⊢ → X ⊢ → Set where
  ξ₁ : {a a' b : X ⊢} → a ⟶ a' → a · b ⟶ a' · b
  -- Value is required in ξ₂ to make this deterministically resolve the left side first
  ξ₂ : {a b b' : X ⊢} → Value a → b ⟶ b' → a · b ⟶ a · b'
  ξ₃ : {a a' : X ⊢} → a ⟶ a' → force a ⟶ force a'
  ξ₄ : {a b c : X ⊢} → a · b ⟶ c → (delay a) · b ⟶ c
  β : {a : (Maybe X) ⊢}{b : X ⊢} → Value b → ƛ a · b ⟶ a [ b ]
  force-delay : {a : X ⊢} → force (delay a) ⟶ a
  -- FIXME: This clashes with force-delay because delay is a Value...
 -- force-value : {a : X ⊢} → Value a → force a ⟶ a

infix 5 _⟶*_
data _⟶*_ {X : Set} : X ⊢ → X ⊢ → Set where
  refl : {M : X ⊢} → M ⟶* M
  trans : { M P N : X ⊢} → M ⟶ P → P ⟶* N → M ⟶* N

tran-⟶* : ∀ {X : Set}{a b c : X ⊢} → a ⟶* b → b ⟶* c → a ⟶* c
tran-⟶* refl b→c = b→c
tran-⟶* (trans x a→b) refl = trans x a→b
tran-⟶* (trans x a→b) (trans x₁ b→c) = trans x (tran-⟶* a→b (trans x₁ b→c))

value-¬⟶ : ∀ {X : Set}{M : X ⊢} → Value M → ¬ (∃[ N ] ( M ⟶ N ))
value-¬⟶ delay (N , ())
value-¬⟶ ƛ (N , ())
value-¬⟶ con (N , ())

⟶-¬value : ∀ {X : Set}{M N : X ⊢} → M ⟶ N → ¬ (Value M)
⟶-¬value {N = N} M⟶N VM = value-¬⟶ VM (N , M⟶N)

⟶-det : ∀ {X : Set}{M N P : X ⊢} → M ⟶ N → M ⟶ P → N ≡ P
⟶-det (ξ₁ n) (ξ₁ p) = cong₂ _·_ (⟶-det n p) refl
⟶-det (ξ₁ n) (ξ₂ x p) = contradiction x (⟶-¬value n)
⟶-det (ξ₂ x n) (ξ₁ p) = contradiction x (⟶-¬value p)
⟶-det (ξ₂ x n) (ξ₂ x₁ p) = cong₂ _·_ refl (⟶-det n p)
⟶-det {M = M} {N = N} {P = P} (ξ₂ delay n) (ξ₄ p) = {!!}
⟶-det (ξ₂ x n) (β x₁) = contradiction x₁ (⟶-¬value n)
⟶-det (ξ₃ n) (ξ₃ p) = cong force (⟶-det n p)
⟶-det (ξ₄ n) (ξ₂ x p) = {!!}
⟶-det (ξ₄ n) (ξ₄ p) = ⟶-det n p
⟶-det (β x) (ξ₂ x₁ p) = contradiction x (⟶-¬value p)
⟶-det (β x) (β x₁) = refl
⟶-det force-delay force-delay = refl
{-
⟶-det (ξ₁ m) (ξ₁ n) = cong₂ _·_ (⟶-det m n) refl
⟶-det (ξ₁ m) (ξ₂ x n) = contradiction x (⟶-¬value m)
⟶-det (ξ₂ x m) (ξ₁ n) = contradiction x (⟶-¬value n)
⟶-det (ξ₂ x m) (ξ₂ x₁ n) = cong₂ _·_ refl (⟶-det m n)
⟶-det (ξ₂ x m) (β x₁) = contradiction x₁ (⟶-¬value m)
⟶-det (ξ₃ m) (ξ₃ n) = cong force (⟶-det m n)
⟶-det (ξ₃ m) (force-value x) = contradiction x (⟶-¬value m)
⟶-det (β x) (ξ₂ x₁ n) = {!!}
⟶-det (β x) (β x₁) = refl
⟶-det force-delay force-delay = refl
⟶-det force-delay (force-value delay) = {!!}
⟶-det (force-value x) (ξ₃ n) = {!!}
⟶-det (force-value delay) force-delay = {!!}
⟶-det (force-value x) (force-value x₁) = refl
-}
{-
⟶-det (ξ₁ m) (ξ₁ n) = cong₂ _·_ (⟶-det m n) refl
⟶-det (ξ₁ m) (ξ₂ x n) = contradiction x (⟶-¬value m)
⟶-det (ξ₂ x m) (ξ₁ n) = contradiction x (⟶-¬value n)
⟶-det (ξ₂ x m) (ξ₂ x₁ n) = cong₂ _·_ refl (⟶-det m n)
⟶-det (ξ₂ x m) (β x₁) = contradiction x₁ (⟶-¬value m)
⟶-det (ξ₃ m) (ξ₃ n) = cong force (⟶-det m n)
⟶-det (β x) (ξ₂ x₁ n) = contradiction x (⟶-¬value n)
⟶-det (β x) (β x₁) = refl
⟶-det force-delay force-delay = refl
-}
```
## Progress
```
variable
  X Y : Set

data Progress (a : X ⊢) : Set where
  step : {b : X ⊢}
        → a ⟶ b
        → Progress a

  done : Value a
        → Progress a

progress : ∀ (M : ⊥ ⊢) → Progress M
progress (` ())
progress (ƛ M) = done ƛ
progress (L · R) with progress L
... | step L⟶L' = step (ξ₁ L⟶L')
... | done VL with progress R
... | step R⟶R' = step (ξ₂ VL R⟶R')
... | done VR with VL -- For the first time I see why Phil prefers typed languages!...
... | delay = {!!}
... | ƛ = step (β VR)
... | con = {!!}
... | error = {!!}
... | builtin = {!!}
progress (force M) with progress M
... | step M⟶M' = step (ξ₃ M⟶M')
... | done delay = step force-delay
... | done ƛ = {!!}
... | done con = {!!}
... | done error = {!!}
... | done builtin = {!!}
progress (delay M) = done delay
progress (con v) = done con
progress (constr i xs) = {!!}
progress (case x ts) = {!!}
progress (builtin b) = done builtin
progress error = done error

```
## "Reduction" Equivalence
```
infix 5 _≅_
data _≅_ {X : Set} : X ⊢ → X ⊢ → Set where
  reduce : {a b c : X ⊢} → a ⟶* c → b ⟶* c → a ≅ b

refl-≅ : ∀{X : Set}{a : X ⊢} → a ≅ a
refl-≅ = reduce refl refl

--tran-≅ : ∀{X : Set}{a b c : X ⊢} → a ≅ b → b ≅ c → a ≅ c
--tran-≅ (reduce p₁ p₂) (reduce p₃ p₄) = reduce {!!} {!!}

--reduce-≅ : ∀{X : Set} {M N : X ⊢} → M ⟶* N → M ≅ N
--reduce-≅ = {!!}

```
## Examples
```
open import RawU using (tag2TyTag; tmCon)
open import Data.Nat using (ℕ)
open import Agda.Builtin.Int using (Int)
open import Data.Empty using (⊥)

integer : RawU.TyTag
integer = tag2TyTag RawU.integer

con-integer : {X : Set} → ℕ → X ⊢
con-integer n = (con (tmCon integer (Int.pos n)))

_ : ƛ (` nothing) · (con-integer {⊥} 42) ⟶ (con-integer 42)
_ = β con

_ : ƛ (` nothing) · (con-integer {⊥} 42) ⟶* (con-integer 42)
_ = trans (β con) refl

_ : ƛ (` nothing) · (con-integer {⊥} 42) ≅ (con-integer 42)
_ = reduce (trans (β con) refl) refl


_ : (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (ƛ (` nothing))) · (con-integer {⊥} 42)) ⟶* (con-integer {⊥} 42)
_ = trans (ξ₁ (β ƛ)) (trans (β con) (trans (β con) refl))

```
Should this work or should un-delayed `error` explode? - It _shouldn't_ work, and doesn't once we have Values.
```
--_ : ((ƛ (ƛ (` (just nothing)))) · (con-integer {⊥} 42)) · error ⟶* (con-integer {⊥} 42)
--_ = trans (ξ₁ (β con)) (trans {!!} refl)
```
Some other examples
```

ex1 : (Maybe ⊥) ⊢
ex1 = (((ƛ (ƛ (((` (just (just nothing))) · (` nothing))) · (` (just nothing))))) · (con-integer {Maybe ⊥} 2)) · (con-integer {Maybe ⊥} 3) --- [[(\× . \y . x - y) 2] 3] ==>  2 - 3

ex2 : (Maybe ⊥) ⊢
ex2 = (((ƛ (ƛ (((` (just (just nothing))) · (` (just nothing))) · (` nothing))))) · (con-integer {Maybe ⊥} 3)) · (con-integer {Maybe ⊥} 2) --- [[(\x . \y . y - x) 3] 2] ==> 2 - 3

--_ : ex1 ≅ ex2
--_ = reduce (trans (ξ₁ (β con)) (trans (ξ₁ {!!}) refl)) (trans (ξ₁ (β con)) (trans (β con) {!!}))
```
