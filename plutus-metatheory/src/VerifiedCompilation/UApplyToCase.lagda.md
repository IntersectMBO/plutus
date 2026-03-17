---
title: VerifiedCompilation.ApplyToCase
layout: page
---

# ApplyToCase Translation Phase

This is the reverse of `CaseReduce`, except that

- The `constr` index must be 0, and case alts must be a singleton.
- There must be at least one argument.
  In other words you can't transform an arbitrary term `M` into `case (constr 0 []) [M]`.

```
module VerifiedCompilation.UApplyToCase where

```
## Imports

```
open import Untyped using (_⊢; case; constr)
open import Untyped.Reduction using (iterApp)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; applyToCaseT)
open import VerifiedCompilation.UCaseReduce using (justEq)
open import VerifiedCompilation.UntypedViews
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation)

open import Function using (case_of_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; _∷_; []; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (trans; sym; subst)
open import Relation.Nullary using (yes; no; ¬_)
```

## Translation Relation

```
data ApplyToCase : Relation where
  a2c :
    {n : ℕ}
    {M M′ : n ⊢}
    {arg : n ⊢}
    {args : List (n ⊢)}
    → Translation ApplyToCase M (iterApp M′ (arg ∷ args))
    → ApplyToCase M (case (constr 0 (arg ∷ args)) [ M′ ])
```
## Decision Procedure

The `TERMINATING` pragma is needed because we recurse into `iterApp M′ (x ∷ xs)`,
which is not smaller than `N`.

```
{-# TERMINATING #-}
a2c?ᶜᶜ : {n : ℕ} → (M N : n ⊢) → ProofOrCE (Translation ApplyToCase M N)

a2c? : {n : ℕ} → (M N : n ⊢) → ProofOrCE (ApplyToCase M N)
a2c? M N with (case? (constr? (_≟_ 0) (⋯ ∷? ⋯)) singleton?) N
... | no ¬p = ce (λ { (a2c _) → ¬p inhabitant } ) applyToCaseT M N
... | yes (case! (constr! refl (match! x ∷! match! xs)) (match! M' ∷! []!))
  with a2c?ᶜᶜ M (iterApp M' (x ∷ xs))
...   | proof p = proof (a2c p)
...   | ce ¬p tag L L′ = ce (λ { (a2c p) → ¬p p }) tag L L′

a2c?ᶜᶜ = translation? applyToCaseT a2c?

UApplyToCase : Relation
UApplyToCase = Translation ApplyToCase
```
