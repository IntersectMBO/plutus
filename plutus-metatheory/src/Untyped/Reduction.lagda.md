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
```
## Values
```

data Value {X : Set} : X ⊢ → Set where
  delay : { a : X ⊢} → Value (delay a)
  ƛ : { a : (Maybe X) ⊢ } → Value (ƛ a)
  con : {n : TmCon} → Value (con n)
-- builtin : {b : Builtin} → Value (builtin b)
-- constr ??? - when all of its arguments are values

```
## Reduction Steps
```

infix 5 _⟶_
data _⟶_ {X : Set} : X ⊢ → X ⊢ → Set where
  ξ₁ : {a a' b : X ⊢} → a ⟶ a' → a · b ⟶ a' · b
  ξ₂ : {a b b' : X ⊢} → b ⟶ b' → a · b ⟶ a · b'
  ξ₃ : {a a' : X ⊢} → a ⟶ a' → force a ⟶ force a'
  β : {a : (Maybe X) ⊢}{b : X ⊢} → Value b → ƛ a · b ⟶ a [ b ]
  force-delay : {a : X ⊢} → force (delay a) ⟶ a

infix 5 _⟶*_
data _⟶*_ {X : Set} : X ⊢ → X ⊢ → Set where
  refl : {a : X ⊢} → a ⟶* a
  trans : { a a' b : X ⊢} → a ⟶ a' → a' ⟶* b → a ⟶* b

tran-⟶* : ∀ {X : Set}{a b c : X ⊢} → a ⟶* b → b ⟶* c → a ⟶* c
tran-⟶* refl b→c = b→c
tran-⟶* (trans x a→b) refl = trans x a→b
tran-⟶* (trans x a→b) (trans x₁ b→c) = trans x (tran-⟶* a→b (trans x₁ b→c))

value-¬⟶ : ∀ {X : Set}{M : X ⊢} → Value M → ¬ (∃[ N ] ( M ⟶ N ))
value-¬⟶ delay (N , ())
value-¬⟶ ƛ (N , ())
value-¬⟶ con (N , ())

⟶-det : ∀ {X : Set}{M N P : X ⊢} → M ⟶ N → M ⟶ P → N ≡ P
⟶-det (ξ₁ M⟶N) (ξ₁ M⟶P) = cong₂ _·_ (⟶-det M⟶N M⟶P) refl
⟶-det (ξ₁ M⟶N) (ξ₂ M⟶P) = ?
⟶-det (ξ₂ M⟶N) (ξ₁ M⟶P) = ?
⟶-det (ξ₂ M⟶N) (ξ₂ M⟶P) = {!!}
⟶-det (ξ₂ M⟶N) (β x) = {!!}
⟶-det (ξ₃ M⟶N) M⟶P = {!!}
⟶-det (β x) M⟶P = {!!}
⟶-det force-delay M⟶P = {!!}

```
## Equivalence
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
