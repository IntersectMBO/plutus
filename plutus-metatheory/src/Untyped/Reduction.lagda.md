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
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂;_≢_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_; _<?_; _≤_)
open import Data.Nat.Properties using (suc-injective)
open import Data.List using (List; []; _∷_)
open import Untyped.CEK using (BUILTIN'; lookup?)
open import Data.List.Relation.Unary.All using (All)
import Relation.Binary.PropositionalEquality as Eq using (subst; trans; sym)
open import Relation.Nullary using (yes;no)
```
## Saturation

Builtins have a defined arity, and then reduce once this is satisfied.
```
data Arity : Set where
  want : ℕ → ℕ → Arity
  interleaving-error : Arity
  over-saturation : Arity

want-injective₀ : {a₀ a₁ b₀ b₁ : ℕ} → want a₀ a₁ ≡ want b₀ b₁ → a₀ ≡ b₀
want-injective₀ refl = refl

want-injective₁ : {a₀ a₁ b₀ b₁ : ℕ} → want a₀ a₁ ≡ want b₀ b₁ → a₁ ≡ b₁
want-injective₁ refl = refl

variable
  X Y : Set

data Value {X : Set} : X ⊢ → Set

data Sign : Set where
  nil : Sign
  force : Sign → Sign
  arg : Sign → Sign

_^_ : ∀ {A : Set} → (A → A) → ℕ → (A → A)
(f ^ zero) x = x
(f ^ (suc n)) x = f ((f ^ n) x)

makeSign : Builtin → Sign
makeSign b = ((arg ^ (arity b)) ((force ^ (arity₀ b)) nil))

data Stack {X : Set} : Sign → X ⊢ → Set where
  builtin : {b : Builtin} → Stack (makeSign b) (builtin b)
  force : {σ : Sign} {t : X ⊢} → Stack (force σ) t → Stack σ (force t)
  app : {σ : Sign} {t v : X ⊢} → Stack (arg σ) t → Stack σ (t · v)

```
## Values
```

data Value {X} where
  delay : {a : X ⊢} → Value (delay a)
  ƛ : {t : (Maybe X) ⊢} → Value (ƛ t)
  con : {n : TmCon} → Value (con n)
  constr : {vs : List (X ⊢)} {n : ℕ} → All Value vs → Value (constr n vs)
  stack : {t : X ⊢} → (σ : Sign) → σ ≢ nil → Stack σ t → Value t

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
  sat-builtin : {t : X ⊢} → Stack nil t → t ⟶ reduceBuiltin t

  case-constr : {i : ℕ} {t : X ⊢} {vs ts : List (X ⊢)}
              → lookup? i ts ≡ just t
              → case (constr i vs) ts ⟶ iterApp t vs
  broken-const : {i : ℕ} {vs ts : List (X ⊢)}
              → lookup? i ts ≡ nothing
              → case (constr i vs) ts ⟶ error
  constr-head-step : {i : ℕ} {v v' : X ⊢} {vs : List (X ⊢)}
              → v ⟶ v'
              → constr i (v ∷ vs) ⟶ constr i (v' ∷ vs)
  constr-tail-step : {i : ℕ} {v : X ⊢} {vs vs' : List (X ⊢)}
              → constr i vs ⟶ constr i vs'
              → constr i (v ∷ vs) ⟶ constr i (v ∷ vs')
  constr-head-error : {i : ℕ} {vs : List (X ⊢)}
              → constr i (error ∷ vs) ⟶ error
  constr-tail-error : {i : ℕ} {v : X ⊢} {vs : List (X ⊢)}
              → constr i vs ⟶ error
              → constr i (v ∷ vs) ⟶ error

  -- Many of the things that you can force that aren't delay
  force-ƛ : {a : Maybe X ⊢} → force (ƛ a) ⟶ error
  force-con : {c : TmCon} → force (con c) ⟶ error
  force-constr : {i : ℕ} {vs : List (X ⊢)} → force (constr i vs) ⟶ error

  force-interleave-error : {t : X ⊢} {σ : Sign} → Stack (arg σ) t → (force t) ⟶ error
  app-interleave-error : {t v : X ⊢} {σ : Sign} → Stack (force σ) t → (t · v) ⟶ error

  -- Many of the things that you can apply to that aren't ƛ
  app-con : {b : X ⊢} {c : TmCon} → (con c) · b ⟶ error
  app-delay : {a b : X ⊢} → (delay a) · b ⟶ error
  app-constr : {b : X ⊢} {i : ℕ} {vs : List (X ⊢)} → (constr i vs) · b ⟶ error

  -- Many of the things that you can case that aren't constr
  case-error : {ts : List (X ⊢)} → case error ts ⟶ error
  case-ƛ : {t : Maybe X ⊢} {ts : List (X ⊢)} → case (ƛ t) ts ⟶ error
  case-delay : {t : X ⊢} {ts : List (X ⊢)} → case (delay t) ts ⟶ error
  case-con : {c : TmCon} {ts : List (X ⊢)} → case (con c) ts ⟶ error
  case-unsat : {t : X ⊢} {ts : List (X ⊢)} {σ : Sign} → σ ≢ nil → Stack σ t → case t ts ⟶ error
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

{-
value-¬⟶ : ∀ {X : Set}{M : X ⊢} → Value M → ¬ (∃[ N ] ( M ⟶ N ))
value-¬⟶ {M = M} delay = λ ()
value-¬⟶ {M = M} ƛ = λ ()
value-¬⟶ {M = M} con = λ ()
value-¬⟶ {M = M} builtin = λ ()
value-¬⟶ {M = M} (unsat₀ x v) = {!!}
value-¬⟶ {M = M} (unsat₀₋₁ x v) = {!!}
value-¬⟶ {M = M} (unsat₁ x v₁ v₂) = {!!}
value-¬⟶ {M = M} (constr x) = {!!}
value-¬⟶ {M = M} error = λ ()

⟶-¬value : ∀ {X : Set}{M N : X ⊢} → M ⟶ N → ¬ (Value M)
⟶-¬value {N = N} M⟶N VM = value-¬⟶ VM (N , M⟶N)

⟶-det : ∀ {X : Set}{M N P : X ⊢} → M ⟶ N → M ⟶ P → N ≡ P
⟶-det n p = {!!}
-}

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
progress (ƛ t) = done ƛ
progress (t · t₁) with progress t
... | step t' = step (ξ₁ t')
... | done con = step app-con
... | done (constr x) = step app-constr
... | fail = step error₁
... | done delay = step app-delay
... | done ƛ with progress t₁
...    | step t₁' = step (ξ₂ ƛ t₁')
...    | done v₁ = step (β v₁)
...    | fail = step error₂
progress (t · t₁) | done (stack nil σ≢nil s) = ⊥-elim (σ≢nil refl)
progress (t · t₁) | done (stack (force σ) σ≢nil s) = step (app-interleave-error s)
progress (t · t₁) | done (stack (arg nil) σ≢nil s) = step (sat-builtin (app s))
progress (t · t₁) | done (stack (arg (force σ)) σ≢nil s) = done (stack (force σ) (λ ()) (app s))
progress (t · t₁) | done (stack (arg (arg σ)) σ≢nil s) = done (stack (arg σ) (λ ()) (app s))
progress (force t) with progress t
... | step t' = step (ξ₃ t')
... | done delay = step force-delay
... | done ƛ = step force-ƛ
... | done con = step force-con
... | done (constr x) = step force-constr
... | done (stack nil σ≢nil s) = step (ξ₃ (sat-builtin s))
... | done (stack (force nil) σ≢nil s) = step (sat-builtin (force s))
... | done (stack (force (force σ)) σ≢nil s) = done (stack (force σ) (λ ()) (force s))
... | done (stack (force (arg σ)) σ≢nil s) = done (stack (arg σ) (λ ()) (force s))
... | done (stack (arg σ) σ≢nil s) = step (force-interleave-error s)
... | fail = step force-error
progress (delay t) = done delay
progress (con x) = done con
progress (constr i xs) = {!!}
progress (case t ts) = {!!}
progress (builtin b) with makeSign b in sig-b
... | force σ = done (stack (force σ) (λ ()) {!builtin!})
... | arg σ = {!!}
... | nil rewrite sig-b = step (sat-builtin {!!})
progress error = fail
{-
progress (` ())
progress (ƛ M) = done ƛ
progress (L · R) with progress L
... | fail = step error₁
... | step L⟶L' = step (ξ₁ L⟶L')
... | done VL with progress R
...   | fail = step error₂
...   | step R⟶R' = step (ξ₂ VL R⟶R')
...   | done VR with VL
...     | delay = step app-delay
...     | ƛ = step (β VR)
...     | con = step app-con
...     | constr x = step app-constr
progress ((force t) · R) | done VL | done VR | unsat₀ s v = step (app-interleave-error (sat-force-step {t = t} s))
progress ((force t) · R) | done VL | done VR | unsat₀₋₁ s v with sat (force t) in sat-ft
... | no-builtin = contradiction (Eq.trans (Eq.sym sat-ft) (sat-force-step {t = t} s)) λ ()
... | interleave-error = {!!}
... | want zero zero = step (ξ₁ (sat-builtin sat-ft)) -- step (ξ₁ (sat-force-builtin sat-ft))
... | want zero (suc zero)  = step (sat-builtin {!!}) --step (sat-app-builtin (sat-app-step {t = force t} {t₁ = R} sat-ft))
... | want zero (suc (suc a₁)) = done (unsat₁ sat-ft VL VR)
... | want (suc a₀) a₁ = step (app-interleave-error sat-ft)
progress ((t · t₁) · R) | done VL | done VR | unsat₁ sat-l≡want v v₁ with sat (t · t₁) in sat-L
...       | no-builtin = contradiction (Eq.trans (Eq.sym (sat-app-step {t = t} {t₁ = t₁} sat-l≡want)) sat-L ) λ ()
...       | interleave-error = {!!}
...       | want (suc a₀) a₁ = step (app-interleave-error sat-L)
...       | want zero zero = {!!} -- step (ξ₁ (sat-app-builtin sat-L))
...       | want zero (suc zero) = {!!} -- step (sat-app-builtin (sat-app-step {t = t · t₁} {t₁ = R} sat-L))
...       | want zero (suc (suc a₁)) = done (unsat₁ sat-L VL VR)
progress ((builtin b) · R) | done VL | done VR | builtin with arity b in arity-b
... | a₁ with arity₀ b in arity₀-b
...   | suc a₀ = step (app-interleave-error (cong₂ want arity₀-b arity-b))
progress (builtin b · R) | done VL | done VR | builtin | suc zero | zero  = {!!} -- step (sat-app-builtin (sat-app-step {t = (builtin b)} {t₁ = R} (cong₂ want arity₀-b arity-b)))
progress (builtin b · R) | done VL | done VR | builtin | suc (suc a₁) | zero  = done (unsat₁ (cong₂ want arity₀-b arity-b) VL VR)
progress (force m) with progress m
... | step x = step (ξ₃ x)
... | fail = step force-error
... | done x with sat m in sat-m
...   | interleave-error = {!!}
...   | want zero a₁ = step (force-interleave-error sat-m)
...   | want (suc (suc a₀)) a₁ = done (unsat₀ sat-m x)
...   | want (suc zero) zero = {!!} -- step (sat-force-builtin (sat-force-step {t = m} sat-m))
...   | want (suc zero) (suc a₁) = done (unsat₀₋₁ sat-m x)
progress (force (ƛ m)) | done Vm | no-builtin = step force-ƛ
progress (force (m · m₁)) | done (unsat₁ sat-m≡want Vm Vm₁) | no-builtin = contradiction (Eq.trans (Eq.sym sat-m) (sat-app-step {t = m} {t₁ = m₁} sat-m≡want)) λ ()
progress (force (force m)) | done (unsat₀ sat-m≡want v) | no-builtin = contradiction (Eq.trans (Eq.sym sat-m) (sat-force-step {t = m} sat-m≡want)) λ ()
progress (force (force m)) | done (unsat₀₋₁ sat-m≡want v) | no-builtin = contradiction (Eq.trans (Eq.sym sat-m) (sat-force-step {t = m} sat-m≡want)) λ ()
progress (force (delay m)) | done Vm | no-builtin = step force-delay
progress (force (con x)) | done Vm | no-builtin = step force-con
progress (force (constr i xs)) | done Vm | no-builtin = step force-constr
progress (force (case m ts)) | done () | no-builtin
progress (force error) | done Vm | no-builtin = step force-error

progress (delay M) = done delay
progress (con v) = done con
progress (constr i []) = done (constr All.[])
progress (constr i (x ∷ xs)) with progress x
... | step x₁ = step (constr-step x₁)
... | fail = step constr-error
... | done x₁ with progress (constr i xs)
...   | done x₂ = done (constr (x₁ All.∷ (value-constr-recurse x₂)))
... | step (constr-step x₂) = step (constr-sub-step (constr-step x₂))
... | step (constr-sub-step x₂) = step (constr-sub-step (constr-sub-step x₂))
... | step constr-error = step (constr-sub-error constr-error)
... | step (constr-sub-error x₂) = step (constr-sub-error (constr-sub-error x₂))
progress (case (ƛ x) ts) = step case-ƛ
progress (case (x · x₁) ts) with progress (x · x₁)
... | step x₂ = step (case-reduce x₂)
... | done (unsat₁ s Vm Vm₁) = step (case-unsat₁ (sat-app-step {t = x} {t₁ = x₁} s))
progress (case (force x) ts) with progress (force x)
... | step x₁ = step (case-reduce x₁)
... | done (unsat₀ s Vm) = step (case-unsat₀ (sat-force-step {t = x} s))
... | done (unsat₀₋₁ s Vm) = step (case-unsat₁ (sat-force-step {t = x} s))
progress (case (delay x) ts) = step case-delay
progress (case (con x) ts) = step case-con
progress (case (constr i xs) ts) with lookup? i ts in lookup-i
... | nothing = step (broken-const lookup-i)
... | just t = step (case-constr lookup-i)
progress (case (case x ts₁) ts) with progress (case x ts₁)
... | step x' = step (case-reduce x')
... | done ()
progress (case (builtin b) ts) = step case-builtin
progress (case error ts) = step case-error
progress (builtin b) = done builtin
progress error = fail
-}
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
