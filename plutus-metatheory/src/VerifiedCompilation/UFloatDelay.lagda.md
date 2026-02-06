---
title: VerifiedCompilation.UFloatDelay
layout: page
---

# Float-Delay Translation Phase
```
module VerifiedCompilation.UFloatDelay where

```
## Imports

```
open import Untyped.Equality using (DecEq; _≟_;decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; isVar?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay; isvar)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation; convert; reflexive)
open import Relation.Nullary using (_×-dec_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_)
open import Data.Empty using (⊥)
open import Function using (case_of_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.List using (map; all)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary as Binary using (Decidable)
open import Data.Product using (_,_)
open import Data.Fin using (Fin;suc;zero)
import Data.Fin.Properties
open import Data.Nat using (ℕ;suc)
open import Data.List using (List)
open import Builtin using (Builtin)
open import RawU using (TmCon)
open import Untyped.Purity using (Pure; isPure?)
open import Data.List.Relation.Unary.All using (All; all?)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; Decider; Certifier; runDecider)
open import VerifiedCompilation.Trace

variable
  X : ℕ
  x x' y y' : X ⊢
```
## Translation Relation

This translation "floats" delays in applied terms into the abstraction, without inlining the whole term.
This is separate from inlining because the added `delay` may make it seem like a substantial increase in code
size, and so dissuade the inliner from executing. However, it may be that the laziness inside the resulting term
is more computationally efficient.

This translation will only preserve semantics if the instances of the bound variable are under a `force` and if the applied term is "Pure".

This requires a function to check all the bound variables are under `force`. The `AllForced` type
is defined in terms of the de Brujin index of the bound variable, since this will be incremented under
further lambdas.
```

data AllForced (X : ℕ) : Fin X → (X ⊢) → Set where
  var : (v : Fin X) → {v' : Fin X} → v' ≢ v → AllForced X v (` v')
  forced : (v : Fin X) → AllForced X v (force (` v))
  force : (v : Fin X) → AllForced X v x' → AllForced X v (force x')
  delay : (v : Fin X) → AllForced X v x' → AllForced X v (delay x')
  ƛ : (v : Fin X) → {t : suc X ⊢}
      → AllForced (suc X) (suc v) t
      → AllForced X v (ƛ t)
  app : (v : Fin X)
      → AllForced X v x
      → AllForced X v y
      → AllForced X v (x · y)
  error : {v : Fin X} → AllForced X v error
  builtin : {v : Fin X} → {b : Builtin} → AllForced X v (builtin b)
  con : {v : Fin X} → {c : TmCon} → AllForced X v (con c)
  case : (v : Fin X) → {t : X ⊢} {ts : List (X ⊢)}
      → AllForced X v t
      → All (AllForced X v) ts
      → AllForced X v (case t ts)
  constr : (v : Fin X) → {i : ℕ} {xs : List (X ⊢)}
      → All (AllForced X v) xs
      → AllForced X v (constr i xs)

{-# TERMINATING #-}
isAllForced? : (v : Fin X) → (t : X ⊢) → Dec (AllForced X v t)
isAllForced? v t with isForce? isTerm? t
... | yes (isforce (isterm t)) with isVar? t
...           | no ¬var with isAllForced? v t
...                       | yes allForced = yes (force v allForced)
...                       | no ¬allForced = no λ { (forced .v) → ¬var (isvar v) ; (force .v p) → ¬allForced p }
isAllForced? v t | yes (isforce (isterm _)) | yes (isvar v₁) with Data.Fin.Properties._≟_ v₁ v
...                       | yes refl = yes (forced v)
...                       | no v₁≢v = yes (force v (var v v₁≢v))
isAllForced? v (` x) | no ¬force with Data.Fin.Properties._≟_ x v
... | yes refl = no λ { (var .v x≢v) → x≢v refl}
... | no x≢v = yes (var v x≢v)
isAllForced? {X} v (ƛ t) | no ¬force with isAllForced? {suc X} (suc v) t
... | yes p = yes (ƛ v p)
... | no ¬p = no λ { (ƛ .v p) → ¬p p}
isAllForced? v (t₁ · t₂) | no ¬force with (isAllForced? v t₁) ×-dec (isAllForced? v t₂)
... | yes (pt₁ , pt₂) = yes (app v pt₁ pt₂)
... | no ¬p = no λ { (app .v x₁ x₂) → ¬p (x₁ , x₂)}
isAllForced? v (force t) | no ¬force = no λ { (forced .v) → ¬force (isforce (isterm t)) ; (force .v x) → ¬force (isforce (isterm t)) }
isAllForced? v (delay t) | no ¬force with isAllForced? v t
... | yes p = yes (delay v p)
... | no ¬p = no λ { (delay .v pp) → ¬p pp}
isAllForced? v (con x) | no ¬force = yes con
isAllForced? v (constr i xs) | no ¬force with all? (isAllForced? v) xs
... | yes p = yes (constr v p)
... | no ¬p = no λ { (constr .v p) → ¬p p }
isAllForced? v (case t ts) | no ¬force with (isAllForced? v t) ×-dec (all? (isAllForced? v) ts)
... | yes (p₁ , p₂) = yes (case v p₁ p₂)
... | no ¬p = no λ { (case .v p₁ p₂) → ¬p ((p₁ , p₂)) }
isAllForced? v (builtin b) | no ¬force = yes builtin
isAllForced? v error | no ¬force = yes error
```
The `delay` needs to be added to all bound variables.
```
{-# TERMINATING #-}
subs-delay : {X : ℕ} → (v : Fin (suc X)) → (suc X ⊢) → (suc X ⊢)
subs-delay v (` x) with Data.Fin.Properties._≟_ v x
... | yes refl = (delay (` x))
... | no _ = (` x)
subs-delay v (ƛ t) = ƛ (subs-delay (suc v) t) -- The de Brujin index has to be incremented
subs-delay v (t · t₁) = (subs-delay v t) · (subs-delay v t₁)
subs-delay v (force t) = force (subs-delay v t) -- This doesn't immediately apply Force-Delay
subs-delay v (delay t) = delay (subs-delay v t)
subs-delay v (con x) = con x
subs-delay v (constr i xs) = constr i (map (subs-delay v) xs)
subs-delay v (case t ts) = case (subs-delay v t) (map (subs-delay v) ts)
subs-delay v (builtin b) = builtin b
subs-delay v error = error

```
The translation relation is then fairly striaghtforward.

```
data FlD {X : ℕ}  : (X ⊢) → (X ⊢) → Set where
  floatdelay : {y y' : X ⊢} {x x' : suc X ⊢}
          → Translation FlD (subs-delay zero x) x'
          → Translation FlD y y'
          → Pure y'
          → FlD (ƛ x · (delay y)) (ƛ x' · y')

FloatDelay : {X : ℕ} → (ast : X ⊢) → (ast' : X ⊢) → Set
FloatDelay = Translation FlD

```
## Decision Procedure
```

isFloatDelay? : {X : ℕ} → Decider (FloatDelay {X})

{-# TERMINATING #-}
isFlD? : {X : ℕ} → Decider (FlD {X})
isFlD? ast ast' with (isApp? (isLambda? isTerm?) (isDelay? isTerm?)) ast
... | no ¬match = ce (λ { (floatdelay x x₁ x₂) → ¬match (isapp (islambda (isterm _)) (isdelay (isterm _)))}) floatDelayT ast ast'
... | yes (isapp (islambda (isterm t₁)) (isdelay (isterm t₂))) with (isApp? (isLambda? isTerm?) isTerm?) ast'
... | no ¬match = ce (λ { (floatdelay x x₁ x₂) → ¬match (isapp (islambda (isterm _)) (isterm _))}) floatDelayT ast ast'
... | yes (isapp (islambda (isterm t₁')) (isterm t₂')) with (isFloatDelay? (subs-delay zero t₁) t₁')
...   | ce ¬p t b a = ce (λ { (floatdelay x x₁ x₂) → ¬p x}) t b a
...   | proof t₁=t₁' with (isFloatDelay? t₂ t₂')
...     | ce ¬p t b a = ce (λ { (floatdelay x x₁ x₂) → ¬p x₁}) t b a
...     | proof t₂=t₂' with (isPure? t₂')
...     | no ¬p = ce (λ { (floatdelay x x₁ x₂) → ¬p x₂} ) floatDelayT ast ast'
...     | yes puret₂' = proof (floatdelay t₁=t₁' t₂=t₂' puret₂')

isFloatDelay? = translation? floatDelayT isFlD?

certFloatDelay : Certifier (FloatDelay {0})
certFloatDelay = runDecider isFloatDelay?

```
