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
open import Untyped.RenamingSubstitution using (_[_]; Sub; sub)
open import Data.Maybe using (Maybe; just; nothing)
open import RawU using (TmCon)
open import Builtin using (Builtin; equals; decBuiltin; arity; arity₀)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_; _<?_; _≤_)
open import Data.Nat.Properties using (suc-injective)
open import Data.List using (List; []; _∷_)
open import Untyped.CEK using (BUILTIN'; lookup?; Env; env2sub)
open import Data.List.Relation.Unary.All using (All; map; _∷_; [])
import Relation.Binary.PropositionalEquality as Eq using (subst; trans; sym)
open import Relation.Nullary using (yes;no)
```
## Saturation

Builtins have a defined arity, and then reduce once this is satisfied.
```
data Arity : Set where
  no-builtin : Arity
  want : ℕ → ℕ → Arity

want-injective₀ : {a₀ a₁ b₀ b₁ : ℕ} → want a₀ a₁ ≡ want b₀ b₁ → a₀ ≡ b₀
want-injective₀ refl = refl

want-injective₁ : {a₀ a₁ b₀ b₁ : ℕ} → want a₀ a₁ ≡ want b₀ b₁ → a₁ ≡ b₁
want-injective₁ refl = refl

postulate
  interleave-error : ∀ {A : Set} → A

sat : {X : ℕ} → X ⊢ → Arity
sat (` x) = no-builtin
sat (ƛ t) = no-builtin
sat (t · t₁) with sat t
... | no-builtin = no-builtin
... | want (suc a₀) a₁ = interleave-error -- This reduces to error
... | want zero (suc a₁) = want zero a₁
... | want zero zero = want zero zero -- This should reduce lower down the tree...
sat (force t) with sat t
... | no-builtin = no-builtin
... | want zero zero = interleave-error  -- This reduces to error
... | want (suc a₀) a₁ = want a₀ a₁
... | want zero (suc a₁) = interleave-error -- This reduces to error
sat (delay t) = no-builtin
sat (con x) = no-builtin
sat (constr i xs) = no-builtin
sat (case t ts) = no-builtin
sat (builtin b) = want (arity₀ b) (arity b)
sat error = no-builtin

sat-app-step : {X : ℕ} {a₁ : ℕ} {t t₁ : X ⊢} → sat t ≡ want zero (suc a₁) → sat (t · t₁) ≡ want zero a₁
sat-app-step {t = t} sat-t with sat t
sat-app-step {t = t} sat-t | want zero (suc x₁) = cong (want zero) (suc-injective (want-injective₁ sat-t))

sat-force-step : {X : ℕ} {a₀ a₁ : ℕ} {t : X ⊢} → sat t ≡ want (suc a₀) a₁ → sat (force t) ≡ want a₀ a₁
sat-force-step {t = t} sat-t with sat t
sat-force-step {t = t} refl | want (suc a₀) a₁ = refl

nat-threshold : {a b : ℕ} → a < b → b ≤ (suc a) → b ≡ (suc a)
nat-threshold {zero} {suc zero} a<b b≤sa = refl
nat-threshold {zero} {suc (suc b)} a<b (Data.Nat.s≤s ())
nat-threshold {suc a} {suc b} (Data.Nat.s≤s a<b) (Data.Nat.s≤s b≤sa) = cong suc (nat-threshold a<b b≤sa)

```
## Values
```
variable
  X Y : ℕ

data Value : 0 ⊢ → Set where
  delay : {a : 0 ⊢} → Value (delay a)
  ƛ : {a : (suc 0) ⊢ } → Value (ƛ a)
  con : {n : TmCon} → Value (con n)
  builtin : {b : Builtin} → Value (builtin b)

  -- To be a Value, a term needs to be still unsaturated
  -- after it has been force'd or had something applied
  -- hence, unsat-builtin₀ and unsat-builtin₁ have
  -- (suc (suc _)) requirements.
  unsat₀ : {t : 0 ⊢} {a₀ a₁ : ℕ}
            → sat t ≡ want (suc (suc a₀)) a₁
            → Value t
            → Value (force t)

  -- unsat-builtin₀₋₁ handles the case where
  -- we consume the last type argument but
  -- still have some unsaturated term args.
  unsat₀₋₁ : {t : 0 ⊢} {a₁ : ℕ}
            → sat t ≡ want (suc zero) (suc a₁)
            → Value t
            → Value (force t)

  unsat₁ : {t t₁ : 0 ⊢} {a₁ : ℕ}
            → sat t ≡ want zero (suc (suc a₁))
            → Value t
            → Value t₁
            → Value (t · t₁)

  constr : {vs : List (0 ⊢)} {n : ℕ} → All Value vs → Value (constr n vs)

value-constr-recurse : {i : ℕ} {vs : List (0 ⊢)} → Value (constr i vs) → All Value vs
value-constr-recurse (constr All.[]) = All.[]
value-constr-recurse (constr (px All.∷ x)) = px All.∷ x

```
## Reduction Steps
```

iterApp : {X : ℕ} → X ⊢ → List (X ⊢) → X ⊢
iterApp x [] = x
iterApp x (v ∷ vs) = iterApp (x · v) vs

-- FIXME: This can use the function from CEK but
-- it will require building the correct BApp type...
postulate
  reduceBuiltin : X ⊢ → X ⊢

infix 5 _⟶_
data _⟶_ : 0 ⊢ → 0 ⊢ → Set where
  ξ₁ : {a a' b : 0 ⊢} → a ⟶ a' → a · b ⟶ a' · b
  -- Value is required in ξ₂ to make this deterministically resolve the left side first
  ξ₂ : {a b b' : 0 ⊢} → Value a → b ⟶ b' → a · b ⟶ a · b'
  ξ₃ : {a a' : 0 ⊢} → a ⟶ a' → force a ⟶ force a'
  β : {a : (suc 0) ⊢}{b : 0 ⊢} → Value b → ƛ a · b ⟶ a [ b ]
  force-delay : {a : 0 ⊢} → force (delay a) ⟶ a

  error₁ : {a : 0 ⊢} → (error · a) ⟶ error
  error₂ : {a : 0 ⊢} → (a · error) ⟶ error
  force-error : force error ⟶ error

  -- Builtins that are saturated will reduce
  sat-app-builtin : {t₁ t₂ : 0 ⊢}
              → sat (t₁ · t₂) ≡ want zero zero
              → (t₁ · t₂) ⟶ reduceBuiltin (t₁ · t₂)
  sat-force-builtin : {t : 0 ⊢}
              → sat (force t) ≡ want zero zero
              → (force t) ⟶ reduceBuiltin (force t)

  case-constr : {i : ℕ} {t : 0 ⊢} {vs ts : List (0 ⊢)}
              → lookup? i ts ≡ just t
              → case (constr i vs) ts ⟶ iterApp t vs
  broken-const : {i : ℕ} {vs ts : List (0 ⊢)}
              → lookup? i ts ≡ nothing
              → case (constr i vs) ts ⟶ error
  constr-step : {i : ℕ} {v v' : 0 ⊢} {vs : List (0 ⊢)}
              → v ⟶ v'
              → constr i (v ∷ vs) ⟶ constr i (v' ∷ vs)
  constr-sub-step : {i : ℕ} {v : 0 ⊢} {vs vs' : List (0 ⊢)}
              → constr i vs ⟶ constr i vs'
              → constr i (v ∷ vs) ⟶ constr i (v ∷ vs')
  constr-error : {i : ℕ} {vs : List (0 ⊢)}
              → constr i (error ∷ vs) ⟶ error
  constr-sub-error : {i : ℕ} {v : 0 ⊢} {vs : List (0 ⊢)}
    → constr i vs ⟶ error
    → constr i (v ∷ vs) ⟶ error

  -- Many of the things that you can force that aren't delay
  force-ƛ : {a : suc 0 ⊢} → force (ƛ a) ⟶ error
  force-con : {c : TmCon} → force (con c) ⟶ error
  force-constr : {i : ℕ} {vs : List (0 ⊢)} → force (constr i vs) ⟶ error

  -- Currently, this assumes type arguments have to come first
  force-interleave-error : {a₁ : ℕ} {t : 0 ⊢}
               → sat t ≡ want zero a₁
               → force t ⟶ error
  app-interleave-error : {a₀ a₁ : ℕ} {t t₁ : 0 ⊢}
               → sat t ≡ want (suc a₀) a₁
               → (t · t₁) ⟶ error

  -- Many of the things that you can apply to that aren't ƛ
  app-con : {b : 0 ⊢} {c : TmCon} → (con c) · b ⟶ error
  app-delay : {a b : 0 ⊢} → (delay a) · b ⟶ error
  app-constr : {b : 0 ⊢} {i : ℕ} {vs : List (0 ⊢)} → (constr i vs) · b ⟶ error

  -- Many of the things that you can case that aren't constr
  case-error : {ts : List (0 ⊢)} → case error ts ⟶ error
  case-ƛ : {t : suc 0 ⊢} {ts : List (0 ⊢)} → case (ƛ t) ts ⟶ error
  case-delay : {t : 0 ⊢} {ts : List (0 ⊢)} → case (delay t) ts ⟶ error
  case-con : {c : TmCon} {ts : List (0 ⊢)} → case (con c) ts ⟶ error
  case-builtin : {b : Builtin} {ts : List (0 ⊢)} → case (builtin b) ts ⟶ error
  case-unsat₀ : {t : 0 ⊢} {ts : List (0 ⊢)} {a₀ a₁ : ℕ} → sat t ≡ want (suc a₀) a₁ → case t ts ⟶ error
  case-unsat₁ : {t : 0 ⊢} {ts : List (0 ⊢)} {a₁ : ℕ} → sat t ≡ want zero (suc a₁) → case t ts ⟶ error
  case-reduce :  {t t' : 0 ⊢} {ts : List (0 ⊢)}
              → t ⟶ t'
              → case t ts ⟶ case t' ts


infix 5 _⟶*_
data _⟶*_ : 0 ⊢ → 0 ⊢ → Set where
  refl : {M : 0 ⊢} → M ⟶* M
  trans : { M P N : 0 ⊢} → M ⟶ P → P ⟶* N → M ⟶* N

tran-⟶* : ∀ {a b c : 0 ⊢} → a ⟶* b → b ⟶* c → a ⟶* c
tran-⟶* refl b→c = b→c
tran-⟶* (trans x a→b) refl = trans x a→b
tran-⟶* (trans x a→b) (trans x₁ b→c) = trans x (tran-⟶* a→b (trans x₁ b→c))
```

## Semantics of values

Irreducible terms cannot take a step:

```
irred : 0 ⊢ → Set
irred M = ∀{N} → ¬ (M ⟶ N)
```

Defining `irred` like this, rather than `irred M = ¬ ∃ (λ N → M ⟶ N)` leverages
implicit parameters and makes proofs a bit shorter.

```
value : 0 ⊢ → Set
value M = irred M × ¬ M ≡ error
```

A short lemma about constructors:

```
irred-constr :
  ∀ {i} {Ms : List (0 ⊢)}
  → All value Ms
  → irred (constr i Ms)
irred-constr ((irred-M , ¬err) ∷ vs) step with step
... | constr-step step₁ = irred-M step₁
... | constr-sub-step step₁ = irred-constr vs step₁
... | constr-error = ¬err refl
... | constr-sub-error step₁ = irred-constr vs step₁
```

Unproven lemma about unsaturated built-ins. This will probably change once we have
a better definitions unsaturated built-ins.

First we capture the current definition of unsaturated terms, which is a bit
awkward (it uses `Value` for the sub-expression that can only be an unsaturated
built-in) and incomplete (it disallows interleaving forces and applications):

```
data unsaturated : (0 ⊢) → Set where
  arg-arg :
    ∀ {M N y}
    → sat M ≡ want 0 (suc (suc y))
    → Value M
    → Value N
    → unsaturated (M · N)

  force-force-args :
    ∀ {M x y}
    → sat M ≡ want (suc (suc x)) y
    → Value M
    → unsaturated (force M)

  force-args :
    ∀ {M y}
    → sat M ≡ want 1 (suc y)
    → Value M
    → unsaturated (force M)
```

Then we assume that any such unsaturated built-in is irreducible.

```
postulate
  irred-unsaturated :
    ∀ {M}
    → unsaturated M
    → irred M
```

Any syntactic value is also semantically a value:

```
V-v : ∀ {M : 0 ⊢} → Value M → value M
V-v* : ∀ {Ms : List (0 ⊢)} → All Value Ms → All value Ms
V-v delay            = (λ ()) , λ ()
V-v ƛ                = (λ ()) , λ ()
V-v con              = (λ ()) , λ ()
V-v (constr vs)      = irred-constr (V-v* vs) , λ ()

V-v builtin          = (λ ()) , λ ()
V-v (unsat₀ wants val-M)    = irred-unsaturated (force-force-args wants val-M) , λ ()
V-v (unsat₀₋₁ wants val-M)  = irred-unsaturated (force-args wants val-M) , λ ()
V-v (unsat₁ wants val-M val-N) = irred-unsaturated (arg-arg wants val-M val-N) , λ ()

V-v* [] = []
V-v* (px ∷ xs) = V-v px ∷ V-v* xs
```

The other direction should hold too

```
postulate
  value-Value : ∀ {M : 0 ⊢} → value M → Value M

{-
value-¬⟶ : ∀ {X : ℕ}{M : X ⊢} → Value M → ¬ (∃[ N ] ( M ⟶ N ))
value-¬⟶ {M = M} delay = λ ()
value-¬⟶ {M = M} ƛ = λ ()
value-¬⟶ {M = M} con = λ ()
value-¬⟶ {M = M} builtin = λ ()
value-¬⟶ {M = M} (unsat₀ x v) = {!!}
value-¬⟶ {M = M} (unsat₀₋₁ x v) = {!!}
value-¬⟶ {M = M} (unsat₁ x v₁ v₂) = {!!}
value-¬⟶ {M = M} (constr x) = {!!}
value-¬⟶ {M = M} error = λ ()

⟶-¬value : ∀ {X : ℕ}{M N : X ⊢} → M ⟶ N → ¬ (Value M)
⟶-¬value {N = N} M⟶N VM = value-¬⟶ VM (N , M⟶N)

⟶-det : ∀ {X : ℕ}{M N P : X ⊢} → M ⟶ N → M ⟶ P → N ≡ P
⟶-det n p = {!!}
-}

```
## Progress
```

data Progress : (a : 0 ⊢) → Set where
  step : {a b : 0 ⊢}
        → a ⟶ b
        → Progress a

  done : {a : 0 ⊢}
        → Value a
        → Progress a

  fail : Progress error

{-# TERMINATING #-}
progress : ∀ (M : 0 ⊢) → Progress M
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
... | want zero zero = step (ξ₁ (sat-force-builtin sat-ft))
... | want zero (suc zero)  = step (sat-app-builtin (sat-app-step {t = force t} {t₁ = R} sat-ft))
... | want zero (suc (suc a₁)) = done (unsat₁ sat-ft VL VR)
... | want (suc a₀) a₁ = step (app-interleave-error sat-ft)
progress ((t · t₁) · R) | done VL | done VR | unsat₁ sat-l≡want v v₁ with sat (t · t₁) in sat-L
...       | no-builtin = contradiction (Eq.trans (Eq.sym (sat-app-step {t = t} {t₁ = t₁} sat-l≡want)) sat-L ) λ ()
...       | want (suc a₀) a₁ = step (app-interleave-error sat-L)
...       | want zero zero = step (ξ₁ (sat-app-builtin sat-L))
...       | want zero (suc zero) = step (sat-app-builtin (sat-app-step {t = t · t₁} {t₁ = R} sat-L))
...       | want zero (suc (suc a₁)) = done (unsat₁ sat-L VL VR)
progress ((builtin b) · R) | done VL | done VR | builtin with arity b in arity-b
... | a₁ with arity₀ b in arity₀-b
...   | suc a₀ = step (app-interleave-error (cong₂ want arity₀-b arity-b))
progress (builtin b · R) | done VL | done VR | builtin | suc zero | zero  = step (sat-app-builtin (sat-app-step {t = (builtin b)} {t₁ = R} (cong₂ want arity₀-b arity-b)))
progress (builtin b · R) | done VL | done VR | builtin | suc (suc a₁) | zero  = done (unsat₁ (cong₂ want arity₀-b arity-b) VL VR)
progress (force m) with progress m
... | step x = step (ξ₃ x)
... | fail = step force-error
... | done x with sat m in sat-m
...   | want zero a₁ = step (force-interleave-error sat-m)
...   | want (suc (suc a₀)) a₁ = done (unsat₀ sat-m x)
...   | want (suc zero) zero = step (sat-force-builtin (sat-force-step {t = m} sat-m))
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

```
## "Reduction" Equivalence
```
infix 5 _≅_
data _≅_ : 0 ⊢ → 0 ⊢ → Set where
  reduce : {a b c : 0 ⊢} → a ⟶* c → b ⟶* c → a ≅ b

refl-≅ : ∀{a : 0 ⊢} → a ≅ a
refl-≅ = reduce refl refl

--tran-≅ : ∀{X : ℕ}{a b c : X ⊢} → a ≅ b → b ≅ c → a ≅ c
--tran-≅ (reduce p₁ p₂) (reduce p₃ p₄) = reduce {!!} {!!}

--reduce-≅ : ∀{X : ℕ} {M N : X ⊢} → M ⟶* N → M ≅ N
--reduce-≅ = {!!}

```
## Examples
```
open import RawU using (tag2TyTag; tmCon)
open import Data.Nat using (ℕ)
open import Agda.Builtin.Int using (Int)

integer : RawU.TyTag
integer = tag2TyTag RawU.integer

con-integer : {X : ℕ} → ℕ → X ⊢
con-integer n = (con (tmCon integer (Int.pos n)))

_ : ƛ (` zero) · (con-integer {0} 42) ⟶ (con-integer 42)
_ = β con

_ : ƛ (` zero) · (con-integer {0} 42) ⟶* (con-integer 42)
_ = trans (β con) refl

_ : ƛ (` zero) · (con-integer {0} 42) ≅ (con-integer 42)
_ = reduce (trans (β con) refl) refl


_ : (((ƛ (ƛ ((` (suc zero)) · (` zero)))) · (ƛ (` zero))) · (con-integer {0} 42)) ⟶* (con-integer {0} 42)
_ = trans (ξ₁ (β ƛ)) (trans (β con) (trans (β con) refl))

```
Should this work or should un-delayed `error` explode? - It _shouldn't_ work, and doesn't once we have Values.
```
--_ : ((ƛ (ƛ (` (suc zero)))) · (con-integer {0} 42)) · error ⟶* (con-integer {0} 42)
--_ = trans (ξ₁ (β con)) (trans {!!} refl)
```
Some other examples
```

ex1 : 1 ⊢
ex1 = (((ƛ (ƛ (((` (suc (suc zero))) · (` zero))) · (` (suc zero))))) · (con-integer {1} 2)) · (con-integer {1} 3) --- [[(\× . \y . x - y) 2] 3] ==>  2 - 3

ex2 : 1 ⊢
ex2 = (((ƛ (ƛ (((` (suc (suc zero))) · (` (suc zero))) · (` zero))))) · (con-integer {1} 3)) · (con-integer {1} 2) --- [[(\x . \y . y - x) 3] 2] ==> 2 - 3

--_ : ex1 ≅ ex2
--_ = reduce (trans (ξ₁ (β con)) (trans (ξ₁ {!!}) refl)) (trans (ξ₁ (β con)) (trans (β con) {!!}))
```
