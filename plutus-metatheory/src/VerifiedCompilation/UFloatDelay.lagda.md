---
title: VerifiedCompilation.UForceDelay
layout: page
---

# Force-Delay Translation Phase
```
module VerifiedCompilation.UFloatDelay where

```
## Imports

```
open import VerifiedCompilation.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation; convert; reflexive)
open import Relation.Nullary.Product using (_×-dec_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥)
open import Function using (case_of_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.List using (map)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary as Binary using (Decidable)
open import Data.Product using (_,_)

```
## Translation Relation

This translation "floats" delays in applied terms into the abstraction, without inlining the whole term.
This is separate from inlining because the added `delay` may make it seem like a substantial increase in code
size, and so dissuade the inliner from executing. However, it may be that the laziness inside the resulting term
is more computationally efficient.

This requires a function to substitute the delay into an abstraction without doing full β-substitution.
```

{-# TERMINATING #-}
subs-delay : {X : Set}{{de : DecEq X}} → (v : Maybe X) → (Maybe X ⊢) → (Maybe X ⊢)
subs-delay v (` x) with v ≟ x
... | yes refl = (delay (` x))
... | no _ = (` x)
subs-delay v (ƛ t) = ƛ (subs-delay (just v) t) -- The de Brujin index has to be incremented
subs-delay v (t · t₁) = (subs-delay v t) · (subs-delay v t₁)
subs-delay v (force t) = force (subs-delay v t) -- This doesn't immediately apply Force-Delay
subs-delay v (delay t) = delay (subs-delay v t)
subs-delay v (con x) = con x
subs-delay v (constr i xs) = constr i (map (subs-delay v) xs)
subs-delay v (case t ts) = case (subs-delay v t) (map (subs-delay v) ts)
subs-delay v (builtin b) = builtin b
subs-delay v error = error

{-
_ : (subs-delay (ƛ ((` nothing) · (ƛ (` (just nothing)))))) ≡ ?
_ = ?
-}
```
The translation relation is then fairly striaghtforward.

```
data FlD {X : Set} {{de : DecEq X}} : (X ⊢) → (X ⊢) → Set₁ where
  floatdelay : {y y' : X ⊢} {x x' : (Maybe X) ⊢}
          → Translation FlD (subs-delay nothing x) x'
          → Translation FlD y y'
          → FlD (ƛ x · (delay y)) (ƛ x' · y')
```
## Decision Procedure
```

isFloatDelay? : {X : Set} {{de : DecEq X}} → Binary.Decidable (Translation FlD {X})

{-# TERMINATING #-}
isFlD? : {X : Set} {{de : DecEq X}} → Binary.Decidable (FlD {X})
isFlD? {{de}} ast ast' with (isApp? (isLambda? isTerm?) (isDelay? isTerm?) ast) ×-dec ((isApp? (isLambda? isTerm?) isTerm?) ast')
... | no ¬p = no λ { (floatdelay x x₁) → ¬p (isapp (islambda (isterm _)) (isdelay (isterm _)) , isapp (islambda (isterm _)) (isterm _))}
... | yes (isapp (islambda (isterm x)) (isdelay (isterm y)) , isapp (islambda (isterm x')) (isterm y')) with (isFloatDelay? (subs-delay nothing x) x') ×-dec (isFloatDelay? y y')
... | yes (fst , snd) = yes (floatdelay fst snd)
... | no ¬pp = no λ { (floatdelay x x₁) → ¬pp (x , x₁) }

isFloatDelay? = translation? isFlD?
```
