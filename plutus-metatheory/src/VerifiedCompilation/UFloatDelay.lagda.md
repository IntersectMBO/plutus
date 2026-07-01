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
open import Untyped.Equality using (_≟_)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; isVar?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay; isvar)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.List using (map)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Fin using (Fin;suc;zero)
open import Data.Nat using (ℕ;suc)
open import Untyped.Purity using (Pure; isPure?)
open import VerifiedCompilation.Certificate using (ce; proof; DecidableCE; FloatDelayT)

variable
  X : ℕ
  x x' y y' : X ⊢
```
## Translation Relation

This translation "floats" delays in applied terms into the abstraction, without inlining the whole term.
This is separate from inlining because the added `delay` may make it seem like a substantial increase in code
size, and so dissuade the inliner from executing. However, it may be that the laziness inside the resulting term
is more computationally efficient.

This translation will only preserve semantics if the applied term is "Pure".

The compiler also checks whether the term under the `delay` is "work-free", and that the occurences of the variable
bound in the lambda abstraction are all under a `force`. This is because it's unclear whether the transformation would
actually constitute an optimization otherwise, but these conditions are not necessary for semantic preservation.

We first define an auxiliary function to add `delay` to all bound variables.
```
{-# TERMINATING #-}
subs-delay : {X : ℕ} → (v : Fin (suc X)) → (suc X ⊢) → (suc X ⊢)
subs-delay v (` x) with v ≟ x
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

isFloatDelay? : {X : ℕ} → DecidableCE (FloatDelay {X})

{-# TERMINATING #-}
isFlD? : {X : ℕ} → DecidableCE (FlD {X})
isFlD? ast ast' with (isApp? (isLambda? isTerm?) (isDelay? isTerm?)) ast
... | no ¬match = ce (λ { (floatdelay x x₁ x₂) → ¬match (isapp (islambda (isterm _)) (isdelay (isterm _)))}) FloatDelayT ast ast'
... | yes (isapp (islambda (isterm t₁)) (isdelay (isterm t₂))) with (isApp? (isLambda? isTerm?) isTerm?) ast'
... | no ¬match = ce (λ { (floatdelay x x₁ x₂) → ¬match (isapp (islambda (isterm _)) (isterm _))}) FloatDelayT ast ast'
... | yes (isapp (islambda (isterm t₁')) (isterm t₂')) with (isFloatDelay? (subs-delay zero t₁) t₁')
...   | ce ¬p t b a = ce (λ { (floatdelay x x₁ x₂) → ¬p x}) t b a
...   | proof t₁=t₁' with (isFloatDelay? t₂ t₂')
...     | ce ¬p t b a = ce (λ { (floatdelay x x₁ x₂) → ¬p x₁}) t b a
...     | proof t₂=t₂' with (isPure? t₂')
...     | no ¬p = ce (λ { (floatdelay x x₁ x₂) → ¬p x₂} ) FloatDelayT ast ast'
...     | yes puret₂' = proof (floatdelay t₁=t₁' t₂=t₂' puret₂')

isFloatDelay? = translation? FloatDelayT isFlD?

```
