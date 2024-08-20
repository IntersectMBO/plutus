---
title: VerifiedCompilation.UForceDelay
layout: page
---

# Force-Delay Translation Phase
```
module VerifiedCompilation.UForceDelay where

```
## Imports

```
open import VerifiedCompilation.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation)
open import Relation.Nullary using (_×-dec_)
open import Data.Product using (_,_)
import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Untyped.RenamingSubstitution using (weaken)
```
## Translation Relation

The Force-Delay translation removes the redundant application of the `force` operator to the `delay` operator.

The simplest case of this is where there is a direct application `force (delay t)` that simply cancels out. However,
the translation also applies to nested or repeated applications, e.g. `force (force (delay (delay t)))`.

Additionally, the translation applies where there is a Lambda abstraction paired with an application, so
`force (ƛ (delay t) · t₂)` for example. There can be multiple abstractions and applications, so long as they
cancel out precisely.

`pureFD` is a mathematical expression of the relation. `FD` is more amenable to building a decision procedure.
Ultimately they should be equivalent.

```
data pureFD : Relation where
  forcedelay : {X : Set} → (x x' : X ⊢) → Translation pureFD x x' → pureFD (force (delay x)) x'
  pushfd : {X : Set} → (x : Maybe X ⊢) → (y : X ⊢)
         → pureFD (force ((ƛ x) · y)) ((ƛ (force x)) · y)
  transfd : {X : Set} → (x x'' x' : X ⊢) → Translation pureFD x x'' → Translation pureFD x'' x' → pureFD x x'
  appfd : {X : Set} → (x : Maybe X ⊢) → (y : X ⊢) → pureFD ((ƛ x) · y) (ƛ (x · (weaken y)))
  appfd⁻¹ : {X : Set} → (x : Maybe X ⊢) → (y : X ⊢) → pureFD (ƛ (x · (weaken y))) ((ƛ x) · y)

data FD : ℕ → ℕ → Relation where
  forcefd : (n nₐ : ℕ) → {X : Set} → (x x' : X ⊢) → FD (suc n) nₐ x x' → FD n nₐ (force x) x'
  delayfd : (n nₐ : ℕ) → {X : Set} → (x x' : X ⊢) → FD n nₐ x x' → FD (suc n) nₐ (delay x) x'
  lastdelay : (n nₐ : ℕ) → {X : Set} → (x x' : X ⊢) → Translation (FD zero zero) x x' → FD (suc zero) zero (delay x) x'
  multiappliedfd : (n nₐ : ℕ) → {X : Set} → (x y x' y' : X ⊢)
                   → Translation (FD zero zero) y y'
                   → FD n (suc nₐ) (force x) x'
                   → FD n nₐ (force (x · y)) (x' · y')
  multiabstractfd : (n nₐ : ℕ) → {X : Set} → (x x' : Maybe X ⊢)
                    →  FD n nₐ (force x) x'
                    →  FD n (suc nₐ) (force (ƛ x)) (ƛ x')

ForceDelay : {X : Set} {{_ : DecEq X}} → (ast : X ⊢) → (ast' : X ⊢) → Set₁
ForceDelay = Translation (FD zero zero)
```
## Decision Procedure


```
isForceDelay? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (Translation (FD zero zero) {X})

{-# TERMINATING #-}
isFD? : {X : Set} {{_ : DecEq X}} → (n nₐ : ℕ) → Binary.Decidable (FD n nₐ {X})

isFD? n nₐ ast ast' with isForce? isTerm? ast

-- If it doesn't start with force then it isn't going to match this translation, unless we have some delays left
isFD? zero nₐ ast ast' | no ¬force = no λ { (forcefd .zero .nₐ x .ast' xx) → ¬force (isforce (isterm x)) ; (multiappliedfd .zero .nₐ x y x' y' x₁ xx) → ¬force (isforce (isterm (x · y))) ; (multiabstractfd .zero nₐ x x' xx) → ¬force (isforce (isterm (ƛ x))) }
isFD? (suc n) nₐ ast ast' | no ¬force with (isDelay? isTerm? ast)
... | no ¬delay = no λ { (forcefd .(suc n) .nₐ x .ast' xx) → ¬force (isforce (isterm x)) ; (delayfd .n .nₐ x .ast' xx) → ¬delay (isdelay (isterm x)) ; (lastdelay n nₐ x .ast' x₁) → ¬delay (isdelay (isterm x)) ; (multiappliedfd .(suc n) .nₐ x y x' y' x₁ xx) → ¬force (isforce (isterm (x · y))) ; (multiabstractfd .(suc n) nₐ x x' xx) → ¬force (isforce (isterm (ƛ x))) }
... | yes (isdelay (isterm t)) with (isForceDelay? t ast') ×-dec (n ≟ zero) ×-dec (nₐ ≟ zero)
... | yes (p , refl , refl) = yes (lastdelay zero zero t ast' p)
... | no ¬zero with isFD? n nₐ t ast'
... | no ¬p = no λ { (delayfd .n .nₐ .t .ast' xxx) → ¬p xxx ; (lastdelay n nₐ .t .ast' x) → ¬zero (x , refl , refl)}
... | yes p = yes (delayfd n nₐ t ast' p)

-- If there is an application we can increment the application counter
isFD? n nₐ ast ast' | yes (isforce (isterm t)) with (isApp? isTerm? isTerm?) t
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | yes (isapp (isterm t₁) (isterm t₂)) with (isApp? isTerm? isTerm?) ast'
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | yes (isapp (isterm t₁) (isterm t₂)) | no ¬isApp = no λ { (multiappliedfd .n .nₐ .t₁ .t₂ x' y' x xx) → ¬isApp (isapp (isterm x') (isterm y')) }
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | yes (isapp (isterm t₁) (isterm t₂)) | yes (isapp (isterm t₁') (isterm t₂')) with (isFD? n (suc nₐ) (force t₁) t₁') ×-dec (isForceDelay? t₂ t₂')
... | yes (pfd , pfd2) = yes (multiappliedfd n nₐ t₁ t₂ t₁' t₂' pfd2 pfd)
... | no ¬FD = no λ { (multiappliedfd .n .nₐ .t₁ .t₂ .t₁' .t₂' x xx) → ¬FD (xx , x) }

-- If there is a lambda we can decrement the application counter unless we have reached zero
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | no ¬isApp with (isLambda? isTerm? t)
isFD? n (suc nₐ ) ast ast' | yes (isforce (isterm t)) | no ¬isApp | yes (islambda (isterm t₂)) with (isLambda? isTerm?) ast'
... | no ¬ƛ = no λ { (multiabstractfd .n .nₐ .t₂ x' xx) → ¬ƛ (islambda (isterm x')) }
... | yes (islambda (isterm t₂')) with (isFD? n nₐ (force t₂) t₂')
... | yes p = yes (multiabstractfd n nₐ t₂ t₂' p)
... | no ¬p = no λ { (multiabstractfd .n .nₐ .t₂ .t₂' xx) → ¬p xx }
-- If we have zero in the application counter then we can't descend further
isFD? n zero ast ast' | yes (isforce (isterm t)) | no ¬isApp | yes (islambda (isterm t₂)) = no λ { (forcefd .n .zero .(ƛ t₂) .ast' ()) }

-- If we have matched none of the patterns then we need to consider nesting.
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | no ¬isApp | no ¬ƛ with isFD? (suc n) nₐ t ast'
... | yes p = yes (forcefd n nₐ t ast' p)
... | no ¬p = no λ { (forcefd .n .nₐ .t .ast' xx) → ¬p xx ; (multiappliedfd .n .nₐ x y x' y' x₁ xx) → ¬isApp (isapp (isterm x) (isterm y)) ; (multiabstractfd .n nₐ x x' xx) → ¬ƛ (islambda (isterm x)) }

isForceDelay? = translation? (isFD? zero zero)

```
