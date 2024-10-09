---
title: VerifiedCompilation.UForceDelay
layout: page
---

# Force-Delay Translation Phase
```
module VerifiedCompilation.UInline where

```
## Imports

```
open import VerifiedCompilation.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation; convert; reflexive)
import Relation.Binary as Binary using (Decidable)
open import Untyped.RenamingSubstitution using (_[_])
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Relation.Nullary using (Dec; yes; no; ¬_)

```
## Translation Relation

```
data Inline : Relation where
  inline : {X : Set}{{_ : DecEq X}}(x x' : Maybe X ⊢) (y y' : X ⊢)
         → Inline x x'
         → Inline y y'
         → Inline (ƛ x · y) (x' [ y' ])
```
## Decision Procedure

```
isInline? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (Translation (Inline) {X})

isIl? : {X : Set} {{_ : DecEq X}} → Binary.Decidable Inline
isIl? ast ast' with (isApp? (isLambda? isTerm?) isTerm?) ast
... | no ¬p = no λ { (inline x x' y y' x₁ x₂) → ¬p (isapp (islambda (isterm x)) (isterm y)) }
... | yes (isapp (islambda (isterm x)) (isterm y)) = {!!}

isInline? = translation? isIl?

```
