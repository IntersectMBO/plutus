---
title: Type Reduction
layout: page
---

This is an experiment in using a frames to cut down on the number of
rules in a structural presentation of reduction. The original version
of the spec uses this style.

```
module Type.ReductionF where
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

## Frames

A frame corresponds to a type with a hole in it for a missing sub
type. It is indexed by two kinds. The first index is the kind of the
outer type that the frame corresponds to, the second index refers to
the kind of the missing subterm. The frame datatypes has constructors
for all the different places in a type that we might need to make a
hole.

```
data Frame : Kind → Kind → Set where
  -·_     : ∅ ⊢⋆ K → Frame J (K ⇒ J)
  _·-     : {A : ∅ ⊢⋆ K ⇒ J} → Value⋆ A → Frame J K
  -⇒_     : ∅ ⊢⋆ * → Frame * *
  _⇒-     : {A : ∅ ⊢⋆ *} → Value⋆ A → Frame * *
  μ-_     : (B : ∅ ⊢⋆ K) → Frame * ((K ⇒ *) ⇒ K ⇒ *)
  μ_-     : {A : ∅ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *} → Value⋆ A → Frame * K
```

Given a frame and type to plug in to it we can close the frame and
recover a type with no hole. By indexing frames by kinds we can
specify exactly what kind the plug needs to have and ensure we don't
plug in something of the wrong kind. We can also ensure what kind the
returned type will have.

```
closeFrame : Frame K J → ∅ ⊢⋆ J → ∅ ⊢⋆ K
closeFrame (-· B)  A = A · B
closeFrame (_·- A) B = discharge A · B
closeFrame (-⇒ B)  A = A ⇒ B
closeFrame (_⇒- A) B = discharge A ⇒ B
closeFrame (μ_- A) B = μ (discharge A) B
closeFrame (μ- B)  A = μ A B

-- this can also be given by an inductive definition
```


## Reduction

Reduction is intrinsically kind preserving. This doesn't require proof.

```
infix 2 _—→⋆_
infix 2 _—↠⋆_

data _—→⋆_ : ∀{J} → (∅ ⊢⋆ J) → (∅ ⊢⋆ J) → Set where
  frameRule : ∀{K K'} → (f : Frame K K')
    → ∀{A A' : ∅ ⊢⋆ K'} → A —→⋆ A'
    → {B B' : ∅ ⊢⋆ K}
    → B ≡ closeFrame f A
    → B' ≡ closeFrame f A'
      --------------------
    → B —→⋆ B'
    -- ^ explicit equality proofs make pattern matching easier and this uglier

  β-ƛ : Value⋆ B
        -------------------
      → ƛ A · B —→⋆ A [ B ]
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
... | step p  = step (frameRule (μ- B) p refl refl)
... | done VA with progress⋆ B
... | step p  = step (frameRule (μ VA -) p refl refl)
... | done VB = done (V-μ VA VB)
progress⋆ (Π A) = done (V-Π A)
progress⋆ (A ⇒ B) with progress⋆ A
... | step p = step (frameRule (-⇒ B) p refl refl)
... | done VA with progress⋆ B
... | step q  = step (frameRule (VA ⇒-) q refl refl)
... | done VB = done (VA V-⇒ VB)
progress⋆ (ƛ A) = done (V-ƛ A)
progress⋆ (A · B) with progress⋆ A
... | step p = step (frameRule (-· B) p refl refl)
... | done VA with progress⋆ B
... | step p = step (frameRule (VA ·-) p refl refl)
progress⋆ (.(ƛ _) · B) | done (V-ƛ A) | done VB = step (β-ƛ VB)
progress⋆ (con tcn) = done (V-con tcn)
```

## Determinism of Reduction:

A type is a value or it can make a step, but not both:

```
notboth : (A : ∅ ⊢⋆ K) → ¬ (Value⋆ A × (Σ (∅ ⊢⋆ K) (A —→⋆_)))
notboth _ (() , A' , frameRule (-· _) p refl _)
notboth _ (() , A' , frameRule (_ ·-) p refl _)
notboth _ ((V V-⇒ _) , _ , frameRule (-⇒ _) p refl _) =
  notboth _ (V , _ , p)
notboth _ ((_ V-⇒ W) , _ , frameRule (_ ⇒-) p refl _) =
  notboth _ (W , _ , p)
notboth _ (V-μ V _ , _ , frameRule (μ- _) p refl _) =
  notboth _ (V , _ , p)
notboth _ (V-μ _ W , _ , frameRule μ _ - p refl _) =
  notboth _ (W , _ , p)
```

Reduction is deterministic. There is only one possible reduction step
a type can make.

```
det : (p : A —→⋆ B)(q : A —→⋆ B') → B ≡ B'
det (frameRule (-· x₄) p refl refl) (frameRule (-· .x₄) q refl refl) =
  cong (_· _) (det p q)
det (frameRule (-· x₄) p refl refl) (frameRule (x₅ ·-) q refl refl) =
  ⊥-elim (notboth _ (x₅ , _ , p))
det (frameRule (-· x₄) p refl refl) (frameRule (-⇒ x₅) q () x₃)
det (frameRule (-· x₄) p refl refl) (frameRule (x₅ ⇒-) q () x₃)
det (frameRule (-· x₄) p refl refl) (frameRule (μ- B) q () x₃)
det (frameRule (-· x₄) p refl refl) (frameRule μ x₅ - q () x₃)
det (frameRule (x₄ ·-) p refl refl) (frameRule (-· x₅) q refl refl) =
  ⊥-elim (notboth _ (x₄ , _ , q))
det (frameRule (x₄ ·-) p refl refl) (frameRule (x₅ ·-) q refl refl) =
  cong (_ ·_) (det p q)
det (frameRule (x₄ ·-) p refl refl) (frameRule (-⇒ x₅) q () x₃)
det (frameRule (x₄ ·-) p refl refl) (frameRule (x₅ ⇒-) q () x₃)
det (frameRule (x₄ ·-) p refl refl) (frameRule (μ- B) q () x₃)
det (frameRule (x₄ ·-) p refl refl) (frameRule μ x₅ - q () x₃)
det (frameRule (-⇒ x₄) p refl refl) (frameRule (-· x₅) q () x₃)
det (frameRule (-⇒ x₄) p refl refl) (frameRule (x₅ ·-) q () x₃)
det (frameRule (-⇒ x₄) p refl refl) (frameRule (-⇒ .x₄) q refl refl) =
  cong (_⇒ _) (det p q)
det (frameRule (-⇒ x₄) p refl refl) (frameRule (x₅ ⇒-) q refl refl) =
    ⊥-elim (notboth _ (x₅ , _ , p))
det (frameRule (-⇒ x₄) p refl refl) (frameRule (μ- B) q () x₃)
det (frameRule (-⇒ x₄) p refl refl) (frameRule μ x₅ - q () x₃)
det (frameRule (x₄ ⇒-) p refl refl) (frameRule (-· x₅) q () x₃)
det (frameRule (x₄ ⇒-) p refl refl) (frameRule (x₅ ·-) q () x₃)
det (frameRule (x₄ ⇒-) p refl refl) (frameRule (-⇒ x₅) q refl refl) =
  ⊥-elim (notboth _ (x₄ , _ , q))
det (frameRule (x₄ ⇒-) p refl refl) (frameRule (x₅ ⇒-) q refl refl) =
  cong (_ ⇒_) (det p q)
det (frameRule (x₄ ⇒-) p refl refl) (frameRule (μ- B) q () x₃)
det (frameRule (x₄ ⇒-) p refl refl) (frameRule μ x₅ - q () x₃)
det (frameRule (μ- B) p refl refl) (frameRule (-· x₄) q () x₃)
det (frameRule (μ- B) p refl refl) (frameRule (x₄ ·-) q () x₃)
det (frameRule (μ- B) p refl refl) (frameRule (-⇒ x₄) q () x₃)
det (frameRule (μ- B) p refl refl) (frameRule (x₄ ⇒-) q () x₃)
det (frameRule (μ- B) p refl refl) (frameRule (μ- .B) q refl refl) =
  cong (λ A → μ A B) (det p q) 
det (frameRule (μ- B) p refl refl) (frameRule μ x₄ - q refl refl) =
  ⊥-elim (notboth _ (x₄ , _ , p))
det (frameRule μ x₄ - p refl refl) (frameRule (-· x₅) q () x₃)
det (frameRule μ x₄ - p refl refl) (frameRule (x₅ ·-) q () x₃)
det (frameRule μ x₄ - p refl refl) (frameRule (-⇒ x₅) q () x₃)
det (frameRule μ x₄ - p refl refl) (frameRule (x₅ ⇒-) q () x₃)
det (frameRule μ x₄ - p refl refl) (frameRule (μ- B) q refl refl) =
  ⊥-elim (notboth _ (x₄ , _ , q))
det (frameRule μ x₄ - p refl refl) (frameRule μ x₅ - q refl refl) =
  cong (μ _) (det p q) 
det (frameRule (-· x) p refl refl) (β-ƛ x₂) =
  ⊥-elim (notboth (ƛ _) (V-ƛ _ , _ , p))
det (frameRule (_ ·-) p refl refl) (β-ƛ V) = ⊥-elim (notboth _ (V , _ , p))
det (β-ƛ x) (frameRule (-· x₃) q refl refl) =
  ⊥-elim (notboth (ƛ _) (V-ƛ _ , _ , q))
det (β-ƛ V) (frameRule (x₃ ·-) q refl refl) = ⊥-elim (notboth _ (V , _ , q))
det (β-ƛ V) (β-ƛ x₁) = refl
```
