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
open import Relation.Nullary.Product using (_×-dec_)
open import Data.Product using (_,_)
import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
```
## Translation Relation

The Force-Delay translation removes the redundant application of the `force` operator to the `delay` operator.

The simplest case of this is where there is a direct application `force (delay t)` that simply cancels out. However,
the translation also applies to nested or repeated applications, e.g. `force (force (delay (delay t)))`.

Additionally, the translation applies where there is a Lambda abstraction paired with an application, so
`force (ƛ (delay t) · t₂)` for example. There can be multiple abstractions and applications, so long as they
cancel out precisely.

```
data FD : ℕ → ℕ → Relation where
  lastdelay : (n nₐ : ℕ) → {X : Set} → (x x' : X ⊢) → FD (suc zero) nₐ (delay x) x'
  delayfd : (n nₐ : ℕ) → {X : Set} → (x x' : X ⊢) → FD n nₐ x x' → FD (suc n) nₐ (delay x) x'
  forcefd : (n nₐ : ℕ) → {X : Set} → (x x' : X ⊢) → FD (suc n) nₐ x x' → FD n nₐ (force x) x'
{-
  forcedelay : {X : Set} → (x x' : X ⊢) → Translation (FD zero zero) x x' → FD zero zero (force (delay x)) x'
  nestedforcedelay : (nₐ : ℕ) → {X : Set} → (x x'' x' : X ⊢)
                   → FD nₐ (force x) x''
                   → FD nₐ (force (force x)) x'
-}
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
## Quick simple examples
These autocomplete, which is probably a good sign?
```

_ : ForceDelay {⊥} (force ((ƛ (delay error)) · error)) ((ƛ error) · error)
_ = Translation.istranslation (force (ƛ (delay error) · error))
     (ƛ error · error)
     (multiappliedfd zero zero (ƛ (delay error)) error (ƛ error) error
      Translation.error
      (multiabstractfd zero zero (delay error) error
       (forcefd zero zero (delay error) error
        (lastdelay zero zero error error))))

_ : ForceDelay {⊥} (force (((ƛ (ƛ (delay error))) · error) · error)) (((ƛ (ƛ error)) · error) · error)
_ = Translation.istranslation
     (force ((ƛ (ƛ (delay error)) · error) · error))
     ((ƛ (ƛ error) · error) · error)
     (multiappliedfd zero zero (ƛ (ƛ (delay error)) · error) error
      (ƛ (ƛ error) · error) error Translation.error
      (multiappliedfd zero 1 (ƛ (ƛ (delay error))) error (ƛ (ƛ error))
       error Translation.error
       (multiabstractfd zero 1 (ƛ (delay error)) (ƛ error)
        (multiabstractfd zero zero (delay error) error
         (forcefd zero zero (delay error) error
          (lastdelay zero zero error error))))))
_ : ForceDelay {⊥} (force ((ƛ ((ƛ (delay error)) · error)) · error)) (ƛ ((ƛ error) · error) · error)
_ = Translation.istranslation
     (force (ƛ (ƛ (delay error) · error) · error))
     (ƛ (ƛ error · error) · error)
     (multiappliedfd zero zero (ƛ (ƛ (delay error) · error)) error
      (ƛ (ƛ error · error)) error Translation.error
      (multiabstractfd zero zero (ƛ (delay error) · error)
       (ƛ error · error)
       (multiappliedfd zero zero (ƛ (delay error)) error (ƛ error) error
        Translation.error
        (multiabstractfd zero zero (delay error) error
         (forcefd zero zero (delay error) error
          (lastdelay zero zero error error))))))

_ : ForceDelay {⊥} (force (force (delay (delay error)))) error
_ = Translation.istranslation (force (force (delay (delay error))))
     error
     (forcefd zero zero (force (delay (delay error))) error
      (forcefd 1 zero (delay (delay error)) error
       (delayfd 1 zero (delay error) error
        (lastdelay zero zero error error))))

_ : ForceDelay {⊥} (force (force (force (delay (delay (delay error)))))) error
_ = Translation.istranslation
     (force (force (force (delay (delay (delay error)))))) error
     (forcefd zero zero (force (force (delay (delay (delay error)))))
      error
      (forcefd 1 zero (force (delay (delay (delay error)))) error
       (forcefd 2 zero (delay (delay (delay error))) error
        (delayfd 2 zero (delay (delay error)) error
         (delayfd 1 zero (delay error) error
          (lastdelay zero zero error error))))))
_ : ForceDelay {⊥} (force (force (force (delay (delay error))))) (force error)
_ = Translation.force
     (Translation.istranslation (force (force (delay (delay error))))
      error
      (forcefd zero zero (force (delay (delay error))) error
       (forcefd 1 zero (delay (delay error)) error
        (delayfd 1 zero (delay error) error
         (lastdelay zero zero error error)))))

_ : ForceDelay {⊥} (force (force ((ƛ (delay (delay (error)))) · error))) (ƛ error · error)
_ = Translation.istranslation
     (force (force (ƛ (delay (delay error)) · error))) (ƛ error · error)
     (forcefd zero zero (force (ƛ (delay (delay error)) · error))
      (ƛ error · error)
      (multiappliedfd 1 zero (ƛ (delay (delay error))) error (ƛ error)
       error Translation.error
       (multiabstractfd 1 zero (delay (delay error)) error
        (forcefd 1 zero (delay (delay error)) error
         (delayfd 1 zero (delay error) error
          (lastdelay zero zero error error))))))

_ : ForceDelay {⊥} (force (force ((ƛ (ƛ (delay (delay (error)))) · error) · error))) ((ƛ (ƛ error) · error) · error)
_ = Translation.istranslation
     (force (force ((ƛ (ƛ (delay (delay error))) · error) · error)))
     ((ƛ (ƛ error) · error) · error)
     (forcefd zero zero
      (force ((ƛ (ƛ (delay (delay error))) · error) · error))
      ((ƛ (ƛ error) · error) · error)
      (multiappliedfd 1 zero (ƛ (ƛ (delay (delay error))) · error) error
       (ƛ (ƛ error) · error) error Translation.error
       (multiappliedfd 1 1 (ƛ (ƛ (delay (delay error)))) error
        (ƛ (ƛ error)) error Translation.error
        (multiabstractfd 1 1 (ƛ (delay (delay error))) (ƛ error)
         (multiabstractfd 1 zero (delay (delay error)) error
          (forcefd 1 zero (delay (delay error)) error
           (delayfd 1 zero (delay error) error
            (lastdelay zero zero error error))))))))
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
... | no ¬delay = no λ { (lastdelay n .nₐ x .ast') → ¬delay (isdelay (isterm x)) ; (delayfd .n .nₐ x .ast' x₁) → ¬delay (isdelay (isterm x)) ; (forcefd .(suc n) .nₐ x .ast' x₁) → ¬force (isforce (isterm x)) ; (multiappliedfd .(suc n) .nₐ x y x' y' x₁ x₂) → ¬force (isforce (isterm (x · y))) ; (multiabstractfd .(suc n) nₐ x x' x₁) → ¬force (isforce (isterm (ƛ x))) }
... | yes (isdelay (isterm t)) with (n ≟ zero)
... | yes refl = yes (lastdelay nₐ nₐ t ast')
... | no ¬zero with isFD? n nₐ t ast'
... | no ¬p = no λ { (lastdelay n .nₐ .t .ast') → ¬zero refl ; (delayfd .n .nₐ .t .ast' x) → ¬p x }
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
... | no ¬p = no λ { (multiabstractfd .n .nₐ .t₂ .t₂' xx) → ¬p xx}
-- If we have zero in the application counter then we can't descend further
isFD? n zero ast ast' | yes (isforce (isterm t)) | no ¬isApp | yes (islambda (isterm t₂)) = no λ { (forcefd .n .zero .(ƛ t₂) .ast' ()) }

-- If we have matched none of the patterns then we need to consider nesting.
isFD? n nₐ ast ast' | yes (isforce (isterm t)) | no ¬isApp | no ¬ƛ with isFD? (suc n) nₐ t ast'
... | yes p = yes (forcefd n nₐ t ast' p)
... | no ¬p = no λ { (forcefd .n .nₐ .t .ast' x) → ¬p x ; (multiappliedfd .n .nₐ x y x' y' x₁ x₂) → ¬isApp (isapp (isterm x) (isterm y)) ; (multiabstractfd .n nₐ x x' x₁) → ¬ƛ (islambda (isterm x)) }

isForceDelay? = translation? (isFD? zero zero)

```

## An Example

```
ex : ⊥ ⊢
ex = force (delay (force (delay (error))))

_ : isForceDelay? ex error ≡ yes (Translation.istranslation (force (delay (force (delay error))))
                                   error
                                   (forcefd zero zero (delay (force (delay error))) error
                                    (lastdelay zero zero (force (delay error)) error)))
_ = refl

ex' : ⊥ ⊢
ex' = force (force (delay (delay error)))

_ : isForceDelay? ex' error ≡ yes (Translation.istranslation (force (force (delay (delay error))))
                                    error
                                    (forcefd zero zero (force (delay (delay error))) error
                                     (forcefd 1 zero (delay (delay error)) error
                                      (delayfd 1 zero (delay error) error
                                       (lastdelay zero zero error error)))))
_ = refl
```
## Some Deeper Examples
```
ex2 : {X : Set} {{_ : DecEq X}} → {x : X} → X ⊢
ex2 {X} {x} = force (force (force ((ƛ (delay (delay (delay (` (nothing)))))) · (` x))))

_ : {X : Set} {{_ : DecEq X}} → {x : X} → isForceDelay? {X} (ex2 {X} {x}) ((ƛ (` nothing)) · (` x)) ≡ yes (Translation.istranslation
                                                                                                            (force
                                                                                                             (force (force (ƛ (delay (delay (delay (` nothing)))) · ` x))))
                                                                                                            (ƛ (` nothing) · ` x)
                                                                                                            (forcefd zero zero
                                                                                                             (force (force (ƛ (delay (delay (delay (` nothing)))) · ` x)))
                                                                                                             (ƛ (` nothing) · ` x)
                                                                                                             (forcefd 1 zero
                                                                                                              (force (ƛ (delay (delay (delay (` nothing)))) · ` x))
                                                                                                              (ƛ (` nothing) · ` x)
                                                                                                              (multiappliedfd 2 zero (ƛ (delay (delay (delay (` nothing)))))
                                                                                                               (` x) (ƛ (` nothing)) (` x) Translation.var
                                                                                                               (multiabstractfd 2 zero (delay (delay (delay (` nothing))))
                                                                                                                (` nothing)
                                                                                                                (forcefd 2 zero (delay (delay (delay (` nothing)))) (` nothing)
                                                                                                                 (delayfd 2 zero (delay (delay (` nothing))) (` nothing)
                                                                                                                  (delayfd 1 zero (delay (` nothing)) (` nothing)
                                                                                                                   (lastdelay zero zero (` nothing) (` nothing))))))))))
_ = {!!}

ex3 : {X : Set} {{_ : DecEq X}} → {x y z : X} → X ⊢
ex3 {X} {x} {y} {z} = force ((((ƛ (ƛ (ƛ (delay (` (nothing)))))) · (` x)) · (` y)) · (` z))

ex3' : {X : Set} {{_ : DecEq X}} → {x : Maybe (Maybe X)} → {y : Maybe X} → {z : X} → X ⊢
ex3' {X} {x} {y} {z} = force ((ƛ ((ƛ ((ƛ (delay (` (nothing)))) · (` x))) · (` y))) · (` z))


ex3'Proof : {X : Set} {{_ : DecEq X}} → {x : Maybe (Maybe X)} → {y : Maybe X} → {z : X} → isForceDelay? {X} (ex3' {X} {x} {y} {z}) ((ƛ ((ƛ ((ƛ (` (nothing))) · (` x))) · (` y))) · (` z)) ≡ yes (Translation.istranslation
                                                                                                                                                                                                   (force (ƛ (ƛ (ƛ (delay (` nothing)) · ` x) · ` y) · ` z))
                                                                                                                                                                                                   (ƛ (ƛ (ƛ (` nothing) · ` x) · ` y) · ` z)
                                                                                                                                                                                                   (multiappliedfd zero zero
                                                                                                                                                                                                    (ƛ (ƛ (ƛ (delay (` nothing)) · ` x) · ` y)) (` z)
                                                                                                                                                                                                    (ƛ (ƛ (ƛ (` nothing) · ` x) · ` y)) (` z) Translation.var
                                                                                                                                                                                                    (multiabstractfd zero zero (ƛ (ƛ (delay (` nothing)) · ` x) · ` y)
                                                                                                                                                                                                     (ƛ (ƛ (` nothing) · ` x) · ` y)
                                                                                                                                                                                                     (multiappliedfd zero zero (ƛ (ƛ (delay (` nothing)) · ` x)) (` y)
                                                                                                                                                                                                      (ƛ (ƛ (` nothing) · ` x)) (` y) Translation.var
                                                                                                                                                                                                      (multiabstractfd zero zero (ƛ (delay (` nothing)) · ` x)
                                                                                                                                                                                                       (ƛ (` nothing) · ` x)
                                                                                                                                                                                                       (multiappliedfd zero zero (ƛ (delay (` nothing))) (` x)
                                                                                                                                                                                                        (ƛ (` nothing)) (` x) Translation.var
                                                                                                                                                                                                        (multiabstractfd zero zero (delay (` nothing)) (` nothing)
                                                                                                                                                                                                         (forcefd zero zero (delay (` nothing)) (` nothing)
                                                                                                                                                                                                          (lastdelay zero zero (` nothing) (` nothing))))))))))
ex3'Proof = {!!}
```
