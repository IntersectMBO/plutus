---
title: VerifiedCompilation.UCaseReduce
layout: page
---

# Case-Reduce Translation Phase
```
module VerifiedCompilation.UCaseReduce where

```
## Imports

```
open import VerifiedCompilation.Equality using (DecEq; _≟_;decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; isVar?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay; isvar)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation; convert; reflexive)
open import Relation.Nullary.Product using (_×-dec_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Untyped.CEK using (lookup?)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
```

## Translation Relation

```

iterApp : {X : Set} → X ⊢ → List (X ⊢) → X ⊢
iterApp x [] = x
iterApp x (v ∷ vs) = iterApp (x · v) vs

data CaseReduce : Relation where
  casereduce : {X : Set} {{_ : DecEq X}} {x x' vv : X ⊢} {vs vs' xs : List (X ⊢)} {i : ℕ}
                         → just x ≡ lookup? i xs
                         → Translation CaseReduce x x'
                         → Pointwise (Translation CaseReduce) vs vs'
                         → CaseReduce (case (constr i vs) xs) (iterApp x' vs')

```
## Decision Procedure

```
isCaseReduce? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (Translation CaseReduce {X})

isCR? : {X : Set} {{_ : DecEq X}} → Binary.Decidable CaseReduce
isCR? ast ast' with (isCase? (isConstr? allTerms?) allTerms?) ast
... | no ¬p = no λ { (casereduce _ _ _) → ¬p (iscase (isconstr _ (allterms _)) (allterms _)) }
... | yes (iscase (isconstr i (allterms vs)) (allterms xs)) with lookup? i xs
... | just x = ?
... | nothing = {!!}

isCaseReduce? = translation? isCR?

```
