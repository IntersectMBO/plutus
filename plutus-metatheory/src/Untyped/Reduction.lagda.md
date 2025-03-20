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
open import Builtin using (Builtin; equals; decBuiltin; arity)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_)
open import Data.List using (List; []; _∷_)
open import Untyped.CEK using (BUILTIN'; lookup?)
open import Data.List.Relation.Unary.All using (All)
```
## Values
```

data Value {X : Set} : X ⊢ → Set where
  delay : {a : X ⊢} → Value (delay a)
  ƛ : {a : (Maybe X) ⊢ } → Value (ƛ a)
  con : {n : TmCon} → Value (con n)
  builtin : {b : Builtin} → Value (builtin b)
  constr : {vs : List (X ⊢)} {n : ℕ} → All Value vs → Value (constr n vs)
  error : Value error

```
## Saturation

Builtins have a defined arity, and then reduce once this is satisfied.
```

saturation : {X : Set} → X ⊢ → Maybe (ℕ × ℕ)
saturation (builtin b) = just (((arity b), zero))
saturation (t · _) with saturation t
... | nothing = nothing
... | just (arity , apps) = just (arity , suc apps)
saturation (force t) with saturation t
... | nothing = nothing
... | just (arity , apps) = just (arity , suc apps)
saturation _ = nothing


```
## Reduction Steps
```

iterApp : {X : Set} → X ⊢ → List (X ⊢) → X ⊢
iterApp x [] = x
iterApp x (v ∷ vs) = iterApp (x · v) vs

variable
  X Y : Set

-- FIXME: This can use the function from CEK but
-- it will require building the correct BApp type...
postulate
  reduceBuiltin : X ⊢ → X ⊢

infix 5 _⟶_
data _⟶_ {X : Set} : X ⊢ → X ⊢ → Set where
  ξ₁ : {a a' b : X ⊢} → a ⟶ a' → a · b ⟶ a' · b
  -- Value is required in ξ₂ to make this deterministically resolve the left side first
  ξ₂ : {a b b' : X ⊢} → Value a → b ⟶ b' → a · b ⟶ a · b'
  ξ₃ : {a a' : X ⊢} → a ⟶ a' → force a ⟶ force a'
  β : {a : (Maybe X) ⊢}{b : X ⊢} → Value b → ƛ a · b ⟶ a [ b ]
  force-delay : {a : X ⊢} → force (delay a) ⟶ a
  error₁ : {a : X ⊢} → (error · a) ⟶ error
  error₂ : {a : X ⊢} → (a · error) ⟶ error
  force-error : force error ⟶ error

  -- Builtins that are saturated will reduce
  sat-builtin : {b : Builtin} {arity args : ℕ} {t a : X ⊢}
              → saturation t ≡ just (arity , args)
              → arity ≡ args
              → (t · a) ⟶ reduceBuiltin (t · a)

  case-constr : {i : ℕ} {t : X ⊢} {vs ts : List (X ⊢)}
              → lookup? i ts ≡ just t
              → case (constr i vs) ts ⟶ iterApp t vs

  -- Many of the things that you can force that aren't delay
  force-ƛ : {a : Maybe X ⊢} → force (ƛ a) ⟶ error
  force-con : {c : TmCon} → force (con c) ⟶ error
  force-app : {a b : X ⊢} → force (a · b) ⟶ error
  force-constr : {i : ℕ} {vs : List (X ⊢)} → force (constr i vs) ⟶ error

  -- Many of the things that you can apply to that aren't ƛ
  app-con : {b : X ⊢} {c : TmCon} → (con c) · b ⟶ error
  app-delay : {a b : X ⊢} → (delay a) · b ⟶ error
  app-constr : {b : X ⊢} {i : ℕ} {vs : List (X ⊢)} → (constr i vs) · b ⟶ error

  -- Many of the things that you can case that aren't constr


infix 5 _⟶*_
data _⟶*_ {X : Set} : X ⊢ → X ⊢ → Set where
  refl : {M : X ⊢} → M ⟶* M
  trans : { M P N : X ⊢} → M ⟶ P → P ⟶* N → M ⟶* N

tran-⟶* : ∀ {X : Set}{a b c : X ⊢} → a ⟶* b → b ⟶* c → a ⟶* c
tran-⟶* refl b→c = b→c
tran-⟶* (trans x a→b) refl = trans x a→b
tran-⟶* (trans x a→b) (trans x₁ b→c) = trans x (tran-⟶* a→b (trans x₁ b→c))

value-¬⟶ : ∀ {X : Set}{M : X ⊢} → Value M → ¬ (∃[ N ] ( M ⟶ N ))
value-¬⟶ delay = λ ()
value-¬⟶ ƛ = λ ()
value-¬⟶ con = λ ()
value-¬⟶ builtin = λ ()
value-¬⟶ error = λ ()

⟶-¬value : ∀ {X : Set}{M N : X ⊢} → M ⟶ N → ¬ (Value M)
⟶-¬value {N = N} M⟶N VM = value-¬⟶ VM (N , M⟶N)

⟶-det : ∀ {X : Set}{M N P : X ⊢} → M ⟶ N → M ⟶ P → N ≡ P
⟶-det n p = {!!}

```
## Progress
```

data Progress {X : Set} : (a : X ⊢) → Set where
  step : {a b : X ⊢}
        → a ⟶ b
        → Progress a

  done : {a : X ⊢}
        → Value a
        → Progress a

  fail : Progress error

progress : ∀ (M : ⊥ ⊢) → Progress M
progress (` ())
progress (ƛ M) = done ƛ
progress (L · R) with progress L
... | fail = step error₁
... | step L⟶L' = step (ξ₁ L⟶L')
... | done VL with progress R
...   | fail = step error₂
...   | step R⟶R' = step (ξ₂ VL R⟶R')
...   | done VR with VL -- For the first time I see why Phil prefers typed languages!...
...   | constr allV = step app-constr
...   | ƛ = step (β VR)
...   | delay = step app-delay
...   | con = step app-con
...   | builtin = {!!}
...   | error = step error₁
progress (force m) with progress m
... | fail = step force-error
... | step M⟶M' = step (ξ₃ M⟶M')
... | done delay = step force-delay
... | done ƛ = step force-ƛ
... | done con = step force-con
... | done error = step force-error
... | done builtin = done {!!}
... | done (constr vA) = step force-constr
progress (delay M) = done delay
progress (con v) = done con
progress (constr i xs) = {!!}
progress (case (ƛ x) ts) = {!!}
progress (case (x · x₁) ts) = {!!}
progress (case (force x) ts) = {!!}
progress (case (delay x) ts) = {!!}
progress (case (con x) ts) = {!!}
progress (case (constr i xs) ts) = {!!}
progress (case (case x ts₁) ts) = {!!}
progress (case (builtin b) ts) = {!!}
progress (case error ts) = {!!}
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
