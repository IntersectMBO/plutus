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
open import Builtin using (Builtin; equals; decBuiltin; arity; arity₀)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_; _<?_; _≤_)
open import Data.List using (List; []; _∷_)
open import Untyped.CEK using (BUILTIN'; lookup?)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary using (yes;no)
```
## Saturation

Builtins have a defined arity, and then reduce once this is satisfied.
```
data ℕ⁺ : Set where
  suc : ℕ → ℕ⁺

data Arity : Set where
  no-builtin : Arity
  -- Waiting for force
  want : ℕ → ℕ → Arity

postulate
  impossible : ∀ {A : Set} → A

sat : {X : Set} → X ⊢ → Arity
sat (` x) = no-builtin
sat (ƛ t) = no-builtin
sat (t · t₁) with sat t
... | no-builtin = no-builtin
... | want (suc a₀) a₁ = impossible -- This reduces to error
... | want zero (suc a₁) = want zero a₁
... | want zero zero = want zero zero -- This should reduce lower down the tree...
sat (force t) with sat t
... | no-builtin = no-builtin
... | want zero zero = impossible
... | want (suc a₀) a₁ = want a₀ a₁
... | want zero (suc a₁) = impossible -- This reduces to error
sat (delay t) = no-builtin
sat (con x) = no-builtin
sat (constr i xs) = no-builtin
sat (case t ts) = no-builtin
sat (builtin b) = want (arity₀ b) (arity b)
sat error = no-builtin

sat-app-step : {X : Set} {a₁ : ℕ} {t t₁ : X ⊢} → sat t ≡ want zero (suc a₁) → sat (t · t₁) ≡ want zero a₁
sat-app-step {t = t · t₁} sat-t = {!!}
sat-app-step {t = force t} sat-t = {!!}
sat-app-step {t = builtin b} sat-t = {!!}


nat-threshold : {a b : ℕ} → a < b → b ≤ (suc a) → b ≡ (suc a)
nat-threshold {zero} {suc zero} a<b b≤sa = refl
nat-threshold {zero} {suc (suc b)} a<b (Data.Nat.s≤s ())
nat-threshold {suc a} {suc b} (Data.Nat.s≤s a<b) (Data.Nat.s≤s b≤sa) = cong suc (nat-threshold a<b b≤sa)

```
## Values
```
variable
  X Y : Set

data Value {X : Set} : X ⊢ → Set where
  delay : {a : X ⊢} → Value (delay a)
  ƛ : {a : (Maybe X) ⊢ } → Value (ƛ a)
  con : {n : TmCon} → Value (con n)
  builtin : {b : Builtin} → Value (builtin b)
  unsat₀ : {a₀ a₁ : ℕ} {t : X ⊢}
                → sat t ≡ want (suc a₀) a₁
                → Value t
  unsat₁ : {a₁ : ℕ} {t : X ⊢}
                → sat t ≡ want zero (suc a₁)
                → Value t
  constr : {vs : List (X ⊢)} {n : ℕ} → All Value vs → Value (constr n vs)
  error : Value error

value-constr-recurse : {i : ℕ} {vs : List (X ⊢)} → Value (constr i vs) → All Value vs
value-constr-recurse (constr All.[]) = All.[]
value-constr-recurse (constr (px All.∷ x)) = px All.∷ x

```
## Reduction Steps
```

iterApp : {X : Set} → X ⊢ → List (X ⊢) → X ⊢
iterApp x [] = x
iterApp x (v ∷ vs) = iterApp (x · v) vs

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
  sat-builtin : {t : X ⊢}
              → sat t ≡ want zero zero
              → t ⟶ reduceBuiltin t

  case-constr : {i : ℕ} {t : X ⊢} {vs ts : List (X ⊢)}
              → lookup? i ts ≡ just t
              → case (constr i vs) ts ⟶ iterApp t vs
  broken-const : {i : ℕ} {vs ts : List (X ⊢)}
              → lookup? i ts ≡ nothing
              → case (constr i vs) ts ⟶ error
  constr-step : {i : ℕ} {v v' : X ⊢} {vs : List (X ⊢)}
              → v ⟶ v'
              → constr i (v ∷ vs) ⟶ constr i (v' ∷ vs)
  constr-sub-step : {i : ℕ} {v : X ⊢} {vs vs' : List (X ⊢)}
              → constr i vs ⟶ constr i vs'
              → constr i (v ∷ vs) ⟶ constr i (v ∷ vs')
  constr-error : {i : ℕ} {vs : List (X ⊢)}
              → constr i (error ∷ vs) ⟶ error
  constr-sub-error : {i : ℕ} {v : X ⊢} {vs : List (X ⊢)}
    → constr i vs ⟶ error
    → constr i (v ∷ vs) ⟶ error

  -- Many of the things that you can force that aren't delay
  force-ƛ : {a : Maybe X ⊢} → force (ƛ a) ⟶ error
  force-con : {c : TmCon} → force (con c) ⟶ error
  force-app : {a b : X ⊢} → force (a · b) ⟶ error
  force-constr : {i : ℕ} {vs : List (X ⊢)} → force (constr i vs) ⟶ error

  -- Currently, this assumes type arguments have to come first
  force-interleave-error : {a₁ : ℕ} {t : X ⊢}
               → sat t ≡ want zero a₁
               → force t ⟶ error
  app-interleave-error : {a₀ a₁ : ℕ} {t t₁ : X ⊢}
               → sat t ≡ want (suc a₀) a₁
               → (t · t₁) ⟶ error

  -- Many of the things that you can apply to that aren't ƛ
  app-con : {b : X ⊢} {c : TmCon} → (con c) · b ⟶ error
  app-delay : {a b : X ⊢} → (delay a) · b ⟶ error
  app-constr : {b : X ⊢} {i : ℕ} {vs : List (X ⊢)} → (constr i vs) · b ⟶ error

  -- Many of the things that you can case that aren't constr
  case-error : {ts : List (X ⊢)} → case error ts ⟶ error
  case-ƛ : {t : Maybe X ⊢} {ts : List (X ⊢)} → case (ƛ t) ts ⟶ error
  case-delay : {t : X ⊢} {ts : List (X ⊢)} → case (delay t) ts ⟶ error
  case-con : {c : TmCon} {ts : List (X ⊢)} → case (con c) ts ⟶ error
  case-builtin : {b : Builtin} {ts : List (X ⊢)} → case (builtin b) ts ⟶ error

  case-reduce :  {t t' : X ⊢} {ts : List (X ⊢)}
              → t ⟶ t'
              → case t ts ⟶ case t' ts


infix 5 _⟶*_
data _⟶*_ {X : Set} : X ⊢ → X ⊢ → Set where
  refl : {M : X ⊢} → M ⟶* M
  trans : { M P N : X ⊢} → M ⟶ P → P ⟶* N → M ⟶* N

tran-⟶* : ∀ {X : Set}{a b c : X ⊢} → a ⟶* b → b ⟶* c → a ⟶* c
tran-⟶* refl b→c = b→c
tran-⟶* (trans x a→b) refl = trans x a→b
tran-⟶* (trans x a→b) (trans x₁ b→c) = trans x (tran-⟶* a→b (trans x₁ b→c))

value-¬⟶ : ∀ {X : Set}{M : X ⊢} → Value M → ¬ (∃[ N ] ( M ⟶ N ))
value-¬⟶ v = {!!}

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

{-# TERMINATING #-}
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
...     | delay = step app-delay
...     | ƛ = step (β VR)
...     | con = step app-con
...     | builtin = {!!}
...     | constr x = step app-constr
...     | error = step error₁
...     | unsat₀ x = step (app-interleave-error x)
...     | unsat₁ sat-l≡want with sat L in sat-l
... | want zero (suc zero) = step (sat-builtin {!!})
... | want zero (suc (suc x₁)) = {!!}
progress (force m) with progress m
... | pp = {!!}
progress (delay M) = done delay
progress (con v) = done con
progress (constr i []) = done (constr All.[])
progress (constr i (x ∷ xs)) with progress x
... | step x₁ = step (constr-step x₁)
... | fail = step constr-error
... | done x₁ with progress (constr i xs)
...   | done x₂ = done (constr (x₁ All.∷ (value-constr-recurse x₂)))
{-
...   | step (constr-step x₂) = step (constr-sub-step (constr-step x₂))
...   | step (constr-sub-step x₂) = step (constr-sub-step (constr-sub-step x₂))
...   | step constr-error = step (constr-sub-error constr-error)
...   | step (constr-sub-error x₂) = step (constr-sub-error (constr-sub-error x₂))
-}
progress (case (ƛ x) ts) = step case-ƛ
progress (case (x · x₁) ts) with progress (x · x₁)
... | step x₂ = step (case-reduce x₂)
-- ... | done (unsat-builtin x₂ x₃) = {!!}
progress (case (force x) ts) with progress (force x)
... | step x₁ = step (case-reduce x₁)
-- ... | done (unsat-builtin x₁ x₂) = {!!}
progress (case (delay x) ts) = step case-delay
progress (case (con x) ts) = step case-con
progress (case (constr i xs) ts) with lookup? i ts in lookup-i
... | nothing = step (broken-const lookup-i)
... | just t = step (case-constr lookup-i)
progress (case (case x ts₁) ts) with progress (case x ts₁)
... | step x' = step (case-reduce x')
-- ... | done (unsat-builtin x₁ x₂) = done (unsat-builtin x₁ x₂)
progress (case (builtin b) ts) = step case-builtin
progress (case error ts) = step case-error
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
