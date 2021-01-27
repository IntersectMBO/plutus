---
title: Type Reduction
layout: page
---

```
module Type.Reduction where
```

Right now this file is not used in other things. In the rest of the
formalisation we compute types via NBE. Instead, it acts as a warmup
to understanding reduction of types, progress, etc.

This version of reduction does not compute under binders. The NBE
version does full normalisation.

## Imports

```
open import Type
open import Type.RenamingSubstitution
open import Builtin.Constant.Type
open import Relation.Nullary
open import Data.Product
open import Data.Empty

open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
```

## Values

Values, types in the empty context that cannot reduce any furter,
presented as a predicate. We don't reduce under either lambda or pi
binders here.

```
data Value⋆ : ∅ ⊢⋆ J → Set where

  V-Π : (N : ∅ ,⋆ K ⊢⋆ *)
        -----------------
      → Value⋆ (Π N)

  _V-⇒_ : Value⋆ A
        → Value⋆ B
          --------------
        → Value⋆ (A ⇒ B)

  V-ƛ : (N : ∅ ,⋆ K ⊢⋆ J)
        -----------------
      → Value⋆ (ƛ N)

  V-con : (tcn : TyCon)
          ----------------
        → Value⋆ (con tcn)

  V-μ : Value⋆ A
      → Value⋆ B
        --------------
      → Value⋆ (μ A B)
```

Converting a value back into a term. For this representation of values
this is trivial:

```
discharge : {A : ∅ ⊢⋆ K} → Value⋆ A → ∅ ⊢⋆ K
discharge {A = A} V = A
```

## Reduction

Reduction is intrinsically kind preserving. This doesn't require proof.

```
infix 2 _—→⋆_
infix 2 _—↠⋆_

data _—→⋆_ : (∅ ⊢⋆ J) → (∅ ⊢⋆ J) → Set where
  ξ-⇒₁ : A —→⋆ A'
         -----------------
       → A ⇒ B —→⋆ A' ⇒ B

  ξ-⇒₂ : Value⋆ A
    → B —→⋆ B'
      -----------------
    → A ⇒ B —→⋆ A ⇒ B'

  ξ-·₁ : A —→⋆ A'
         ----------------
       → A · B —→⋆ A' · B

  ξ-·₂ : Value⋆ A
       → B —→⋆ B'
         ----------------
       → A · B —→⋆ A · B'

  β-ƛ : Value⋆ B
        -------------------
      → ƛ A · B —→⋆ A [ B ]

  ξ-μ₁ : A —→⋆ A'
         ----------------
       → μ A B —→⋆ μ A' B

  ξ-μ₂ : Value⋆ A
       → B —→⋆ B'
         ----------------
       → μ A B —→⋆ μ A B'
```

## Reflexive transitie closure of reduction

```
data _—↠⋆_ : (∅ ⊢⋆ J) → (∅ ⊢⋆ J) → Set where

  refl—↠⋆ : --------
             A —↠⋆ A

  trans—↠⋆ : A —→⋆ B
           → B —↠⋆ C
             -------
           → A —↠⋆ C
```

## Progress

An enumeration of possible outcomes of progress: a step or we hit a value.

```
data Progress⋆ (A : ∅ ⊢⋆ K) : Set where
  step : A —→⋆ B
         -----------
       → Progress⋆ A
  done : Value⋆ A
         -----------
       → Progress⋆ A
```

The progress proof. For any type in the empty context we can make
progres. Note that ther is no case for variables as there are no
variables in the empty context.

```
progress⋆ : (A : ∅ ⊢⋆ K) → Progress⋆ A
progress⋆ (` ())
progress⋆ (μ A B) with progress⋆ A
... | step p  = step (ξ-μ₁ p)
... | done VA with progress⋆ B
... | step p  = step (ξ-μ₂ VA p)
... | done VB = done (V-μ VA VB)
progress⋆ (Π A) = done (V-Π A)
progress⋆ (A ⇒ B) with progress⋆ A
... | step p = step (ξ-⇒₁ p)
... | done VA with progress⋆ B
... | step q  = step (ξ-⇒₂ VA q)
... | done VB = done (VA V-⇒ VB)
progress⋆ (ƛ A) = done (V-ƛ A)
progress⋆ (A · B) with progress⋆ A
... | step p = step (ξ-·₁ p)
... | done VA with progress⋆ B
... | step p = step (ξ-·₂ VA p)
progress⋆ (.(ƛ _) · B) | done (V-ƛ A) | done VB = step (β-ƛ VB)
progress⋆ (con tcn) = done (V-con tcn)
```

## Determinism of Reduction:

A type is a value or it can make a step, but not both:

```
notboth : (A : ∅ ⊢⋆ K) → ¬ (Value⋆ A × (Σ (∅ ⊢⋆ K) (A —→⋆_)))
notboth .(_ ⇒ _) ((V V-⇒ W) , .(_ ⇒ _) , ξ-⇒₁ p)   = notboth _ (V , _ , p)
notboth .(_ ⇒ _) ((V V-⇒ W) , .(_ ⇒ _) , ξ-⇒₂ _ p) = notboth _ (W , _ , p)
notboth .(μ _ _) (V-μ V W   , .(μ _ _)  , ξ-μ₁ p)   = notboth _ (V , _ , p)
notboth .(μ _ _) (V-μ V W   , .(μ _ _)  , ξ-μ₂ _ p) = notboth _ (W , _ , p)
```

Reduction is deterministic. There is only one possible reduction step
a type can make.

```
det : (p : A —→⋆ B)(q : A —→⋆ B') → B ≡ B'
det (ξ-⇒₁ p) (ξ-⇒₁ q) = cong (_⇒ _) (det p q)
det (ξ-⇒₁ p) (ξ-⇒₂ w q) = ⊥-elim (notboth _ (w , _ , p))
det (ξ-⇒₂ v p) (ξ-⇒₁ q) = ⊥-elim (notboth _ (v , _ , q))
det (ξ-⇒₂ v p) (ξ-⇒₂ w q) = cong (_ ⇒_) (det p q)
det (ξ-·₁ p) (ξ-·₁ q) = cong (_· _) (det p q)
det (ξ-·₁ p) (ξ-·₂ w q) = ⊥-elim (notboth _ (w , _ , p))
det (ξ-·₂ v p) (ξ-·₁ q) = ⊥-elim (notboth _ (v , _ , q))
det (ξ-·₂ v p) (ξ-·₂ w q) = cong (_ ·_) (det p q)
det (ξ-·₂ v p) (β-ƛ w) = ⊥-elim (notboth _ (w , _ , p))
det (β-ƛ v) (ξ-·₂ w q) = ⊥-elim (notboth _ (v , _ , q))
det (β-ƛ v) (β-ƛ w) = refl
det (ξ-μ₁ p) (ξ-μ₁ q) = cong (λ X → μ X _) (det p q)
det (ξ-μ₁ p) (ξ-μ₂ w q) = ⊥-elim (notboth _ (w , _ , p))
det (ξ-μ₂ v p) (ξ-μ₁ q) = ⊥-elim (notboth _ (v , _ , q))
det (ξ-μ₂ v p) (ξ-μ₂ w q) = cong (μ _) (det p q)
```
