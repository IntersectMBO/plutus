---
title: VerifiedCompilation.UCaseOfCas
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

```
data FD : ℕ → Relation where
  forcedelay : {X : Set} → (x x' : X ⊢) → Translation (FD zero) x x' → FD zero (force (delay x)) x'
  multiappliedfd : (n : ℕ) → {X : Set} → (x y x' y' : X ⊢)
                   → Translation (FD zero) y y'
                   → FD (suc n) (force x) x'
                   → FD n (force (x · y)) (x' · y')
  multiabstractfd : (n : ℕ) → {X : Set} → (x x' : Maybe X ⊢)
                    →  FD n (force x) x'
                    →  FD (suc n) (force (ƛ x)) (ƛ x')

ForceDelay : {X : Set} {{_ : DecEq X}} → (ast : X ⊢) → (ast' : X ⊢) → Set₁
ForceDelay = Translation (FD zero)

-- These autocomplete, which is probably a good sign?
_ : ForceDelay {⊥} (force ((ƛ (delay error)) · error)) ((ƛ error) · error)
_ = Translation.istranslation (force (ƛ (delay error) · error))
     (ƛ error · error)
     (multiappliedfd zero (ƛ (delay error)) error (ƛ error) error
      Translation.error
      (multiabstractfd zero (delay error) error
       (forcedelay error error Translation.error)))

_ : ForceDelay {⊥} (force (((ƛ (ƛ (delay error))) · error) · error)) (((ƛ (ƛ error)) · error) · error)
_ = Translation.istranslation
     (force ((ƛ (ƛ (delay error)) · error) · error))
     ((ƛ (ƛ error) · error) · error)
     (multiappliedfd zero (ƛ (ƛ (delay error)) · error) error
      (ƛ (ƛ error) · error) error Translation.error
      (multiappliedfd 1 (ƛ (ƛ (delay error))) error (ƛ (ƛ error)) error
       Translation.error
       (multiabstractfd 1 (ƛ (delay error)) (ƛ error)
        (multiabstractfd zero (delay error) error
         (forcedelay error error Translation.error)))))

_ : ForceDelay {⊥} (force ((ƛ ((ƛ (delay error)) · error)) · error)) (ƛ ((ƛ error) · error) · error)
_ = Translation.istranslation
     (force (ƛ (ƛ (delay error) · error) · error))
     (ƛ (ƛ error · error) · error)
     (multiappliedfd zero (ƛ (ƛ (delay error) · error)) error
      (ƛ (ƛ error · error)) error Translation.error
      (multiabstractfd zero (ƛ (delay error) · error) (ƛ error · error)
       (multiappliedfd zero (ƛ (delay error)) error (ƛ error) error
        Translation.error
        (multiabstractfd zero (delay error) error
         (forcedelay error error Translation.error)))))


```

## Decision Procedure

```
isForceDelay? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (Translation (FD zero) {X})

{-# TERMINATING #-}
isFD? : {X : Set} {{_ : DecEq X}} → (n : ℕ) → Binary.Decidable (FD n {X})
isFD? n ast ast' with isForce? isTerm? ast
isFD? n ast ast' | no ¬force = no λ { (forcedelay x .ast' x₁) → ¬force (isforce (isterm (delay x))) ; (multiappliedfd .n x y x' y' x₁ xx) → ¬force (isforce (isterm (x · y))) ; (multiabstractfd n x x' xx) → ¬force (isforce (isterm (ƛ x))) }

isFD? n ast ast' | yes (isforce (isterm t)) with isDelay? isTerm? t
isFD? n ast ast' | yes (isforce (isterm _)) | yes (isdelay (isterm t₂)) with (isForceDelay? t₂ ast') ×-dec (n ≟ zero)
... | no ¬FD = no λ { (forcedelay .t₂ .ast' x) → ¬FD (x , refl) }
... | yes (p , refl) = yes (forcedelay t₂ ast' p)

isFD? n ast ast' | yes (isforce (isterm t)) | no ¬delay with (isApp? isTerm? isTerm?) t

isFD? n ast ast' | yes (isforce (isterm t)) | no ¬delay | yes (isapp (isterm t₁) (isterm t₂)) with (isApp? isTerm? isTerm?) ast'
isFD? n ast ast' | yes (isforce (isterm t)) | no ¬delay | yes (isapp (isterm t₁) (isterm t₂)) | no ¬isApp = no λ { (multiappliedfd .n .t₁ .t₂ x' y' x xx) → ¬isApp (isapp (isterm x') (isterm y')) }
isFD? n ast ast' | yes (isforce (isterm t)) | no ¬delay | yes (isapp (isterm t₁) (isterm t₂)) | yes (isapp (isterm t₁') (isterm t₂')) with (isFD? (suc n) (force t₁) t₁') ×-dec (isForceDelay? t₂ t₂')
... | yes (pfd , pfd2) = yes (multiappliedfd n t₁ t₂ t₁' t₂' pfd2 pfd)
... | no ¬FD = no λ { (multiappliedfd .n .t₁ .t₂ .t₁' .t₂' x xx) → ¬FD (xx , x) }

isFD? n ast ast' | yes (isforce (isterm t)) | no ¬delay | no ¬isApp with (isLambda? isTerm? t)
isFD? n ast ast' | yes (isforce (isterm t)) | no ¬delay | no ¬isApp | no ¬ƛ = no λ { (forcedelay x .ast' x₁) → ¬delay (isdelay (isterm x)) ; (multiappliedfd .n x y x' y' x₁ xx) → ¬isApp (isapp (isterm x) (isterm y)) ; (multiabstractfd n x x' xx) → ¬ƛ (islambda (isterm x)) }
isFD? zero ast ast' | yes (isforce (isterm t)) | no ¬delay | no ¬isApp | yes (islambda (isterm t₂)) = no λ ()
isFD? (suc n) ast ast' | yes (isforce (isterm t)) | no ¬delay | no ¬isApp | yes (islambda (isterm t₂)) with (isLambda? isTerm?) ast'
... | no ¬ƛ = no λ { (multiabstractfd .n .t₂ x' xx) → ¬ƛ (islambda (isterm x')) }
... | yes (islambda (isterm t₂')) with (isFD? n (force t₂) t₂')
... | yes p = yes (multiabstractfd n t₂ t₂' p)
... | no ¬p = no λ { (multiabstractfd .n .t₂ .t₂' xxx) → ¬p xxx }

isForceDelay? = translation? (isFD? zero)
```

## An Example

```
ex : ⊥ ⊢
ex = force (delay (force (delay (error))))

_ : isForceDelay? ex error ≡ yes (Translation.istranslation (force (delay (force (delay error))))
                                   error
                                   (forcedelay (force (delay error)) error
                                    (Translation.istranslation (force (delay error)) error
                                     (forcedelay error error Translation.error))))
_ = refl
```
## Some Deeper Examples
```
ex2 : {X : Set} {{_ : DecEq X}} → {x : X} → X ⊢
ex2 {X} {x} = force (force (force ((ƛ (delay (delay (delay (` (nothing)))))) · (` x))))

_ : {X : Set} {{_ : DecEq X}} → {x : X} → isForceDelay? {X} (ex2 {X} {x}) ((ƛ (` nothing)) · (` x)) ≡ yes {!!}
_ = {!!}

ex3 : {X : Set} {{_ : DecEq X}} → {x y z : X} → X ⊢
ex3 {X} {x} {y} {z} = force ((((ƛ (ƛ (ƛ (delay (` (nothing)))))) · (` x)) · (` y)) · (` z))

ex3' : {X : Set} {{_ : DecEq X}} → {x : Maybe (Maybe X)} → {y : Maybe X} → {z : X} → X ⊢
ex3' {X} {x} {y} {z} = force ((ƛ ((ƛ ((ƛ (delay (` (nothing)))) · (` x))) · (` y))) · (` z))


ex3'Proof : {X : Set} {{_ : DecEq X}} → {x : Maybe (Maybe X)} → {y : Maybe X} → {z : X} → isForceDelay? {X} (ex3' {X} {x} {y} {z}) ((ƛ ((ƛ ((ƛ (` (nothing))) · (` x))) · (` y))) · (` z)) ≡ yes (Translation.istranslation
                                                                                                                                                                                                   (force (ƛ (ƛ (ƛ (delay (` nothing)) · ` x) · ` y) · ` z))
                                                                                                                                                                                                   (ƛ (ƛ (ƛ (` nothing) · ` x) · ` y) · ` z)
                                                                                                                                                                                                   (multiappliedfd zero (ƛ (ƛ (ƛ (delay (` nothing)) · ` x) · ` y))
                                                                                                                                                                                                    (` z) (ƛ (ƛ (ƛ (` nothing) · ` x) · ` y)) (` z) Translation.var
                                                                                                                                                                                                    (multiabstractfd zero (ƛ (ƛ (delay (` nothing)) · ` x) · ` y)
                                                                                                                                                                                                     (ƛ (ƛ (` nothing) · ` x) · ` y)
                                                                                                                                                                                                     (multiappliedfd zero (ƛ (ƛ (delay (` nothing)) · ` x)) (` y)
                                                                                                                                                                                                      (ƛ (ƛ (` nothing) · ` x)) (` y) Translation.var
                                                                                                                                                                                                      (multiabstractfd zero (ƛ (delay (` nothing)) · ` x)
                                                                                                                                                                                                       (ƛ (` nothing) · ` x)
                                                                                                                                                                                                       (multiappliedfd zero (ƛ (delay (` nothing))) (` x) (ƛ (` nothing))
                                                                                                                                                                                                        (` x) Translation.var
                                                                                                                                                                                                        (multiabstractfd zero (delay (` nothing)) (` nothing)
                                                                                                                                                                                                         (forcedelay (` nothing) (` nothing) Translation.var))))))))
ex3'Proof = {!!}
```
