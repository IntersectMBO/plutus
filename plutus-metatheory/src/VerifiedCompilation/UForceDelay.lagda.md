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
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation)

import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥)

```
## Translation Relation
```
data FD : Relation where
  forcedelay : {X : Set} → (x x' : X ⊢) → Translation FD x x' → FD (force (delay x)) x'

ForceDelay : {X : Set} {{_ : DecEq X}} → (ast : X ⊢) → (ast' : X ⊢) → Set₁
ForceDelay = Translation FD 
```

## Decision Procedure

```
isForceDelay? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (Translation FD {X})

{-# TERMINATING #-}
isFD? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (FD {X})
isFD? ast ast' with ((isForce? (isDelay? isTerm?)) ast)
... | no ¬p = no λ { (forcedelay x .ast' x₁) → ¬p (isforce (isdelay (isterm x))) }
... | yes (isforce (isdelay (isterm x))) with isForceDelay? x ast'
... | yes p = yes (forcedelay x ast' p)
... | no ¬x≟ast' = no λ { (forcedelay _ _ x) → ¬x≟ast' x }

isForceDelay? = translation? isFD?
```

## An Example

```
ex : ⊥ ⊢
ex = force (delay (force (delay (error))))

_ : isForceDelay? ex error ≡ yes (Translation.istranslation ex error (forcedelay (force (delay error)) error
                                                                       (Translation.istranslation (force (delay error)) error
                                                                        (forcedelay error error Translation.error))))
_ = refl
```
