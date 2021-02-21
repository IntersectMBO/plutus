---
title: Type Reduction, contextual style
layout: page
---

```
module Type.ReductionC where
```

The rules are presented in 'contextual style' with a first order
presentation of closing an evaluation context.

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

## Eval contexts

```
data EvalCtx : (K J : Kind) → Set where
  []   : EvalCtx K K
  _·r_ : {A : ∅ ⊢⋆ K ⇒ J} → Value⋆ A → EvalCtx K I → EvalCtx J I
  _l·_ : EvalCtx (K ⇒ J) I → (∅ ⊢⋆ K) → EvalCtx J I
  _⇒r_     : {A : ∅ ⊢⋆ *} → Value⋆ A → EvalCtx * I → EvalCtx * I
  _l⇒_     : EvalCtx * I → (∅ ⊢⋆ *) → EvalCtx * I
  μr     : {A : ∅ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *} → Value⋆ A → EvalCtx K I → EvalCtx * I
  μl     : EvalCtx ((K ⇒ *) ⇒ K ⇒ *) I →  (B : ∅ ⊢⋆ K) → EvalCtx * I

closeEvalCtx : EvalCtx K J → ∅ ⊢⋆ J → ∅ ⊢⋆ K
closeEvalCtx []       C = C
closeEvalCtx (V ·r E) C = discharge V · closeEvalCtx E C
closeEvalCtx (E l· B) C = closeEvalCtx E C · B
closeEvalCtx (V ⇒r E) C = discharge V ⇒ closeEvalCtx E C
closeEvalCtx (E l⇒ B) C = closeEvalCtx E C ⇒ B
closeEvalCtx (μr V E) C = μ (discharge V) (closeEvalCtx E C)
closeEvalCtx (μl E B) C = μ (closeEvalCtx E C) B

data _~_⟦_⟧ : ∅ ⊢⋆ K → EvalCtx K J → ∅ ⊢⋆ J → Set where
  ~[] : (P : ∅ ⊢⋆ K) → P ~ [] ⟦ P ⟧
  ~·r : ∀(P : ∅ ⊢⋆ I){A : ∅ ⊢⋆ K ⇒ J}(V : Value⋆ A)(B : ∅ ⊢⋆ K) E
      → B ~ E ⟦ P ⟧
      → (discharge V · B) ~ V ·r E ⟦ P ⟧
  ~l· : ∀(P : ∅ ⊢⋆ I)(A : ∅ ⊢⋆ K ⇒ J)(B : ∅ ⊢⋆ K) E
      → A ~ E ⟦ P ⟧
      → (A · B) ~ E l· B ⟦ P ⟧
  ~⇒r : ∀(P  : ∅ ⊢⋆ K) A (V : Value⋆ A) E B
      → B ~ E ⟦ P ⟧
      → (A ⇒ B) ~ V ⇒r E ⟦ P ⟧  
  ~l⇒ : ∀(P  : ∅ ⊢⋆ K) A B E
      → A ~ E ⟦ P ⟧
      → (A ⇒ B) ~ E l⇒ B ⟦ P ⟧  
  ~μr : ∀(P  : ∅ ⊢⋆ I) A (V : Value⋆ A) E (B : ∅ ⊢⋆ K)
      → B ~ E ⟦ P ⟧
      → (μ A B) ~ (μr V E) ⟦ P ⟧  
  ~μl : ∀(P  : ∅ ⊢⋆ I) A (B : ∅ ⊢⋆ K) E
      → A ~ E ⟦ P ⟧
      → (μ A B) ~ (μl E B) ⟦ P ⟧  
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
  contextRule : ∀{K K'} → (E : EvalCtx K K')
    → ∀{A A' : ∅ ⊢⋆ K'}
    → A —→⋆ A'
    → {B B' : ∅ ⊢⋆ K}
    → B  ~ E ⟦ A ⟧
    → B' ~ E ⟦ A' ⟧
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
progres. Note that there is no case for variables as there are no
variables in the empty context.

```
progress⋆ : (A : ∅ ⊢⋆ K) → Progress⋆ A
progress⋆ (` ())
progress⋆ (μ A B) with progress⋆ A
... | step p  = step (contextRule (μl [] B) p (~μl A A B [] (~[] A)) (~μl _ _ B [] (~[] _)))
... | done VA with progress⋆ B
... | step p  = step (contextRule (μr VA []) p (~μr B A VA [] B (~[] B)) (~μr _ A VA [] _ (~[] _)))
... | done VB = done (V-μ VA VB)
progress⋆ (Π A) = done (V-Π A)
progress⋆ (A ⇒ B) with progress⋆ A
... | step p = step (contextRule ([] l⇒ B) p (~l⇒ A A B [] (~[] A)) (~l⇒ _ _ _ [] (~[] _)))
... | done VA with progress⋆ B
... | step q  = step (contextRule (VA ⇒r []) q (~⇒r B _ VA [] B (~[] B)) (~⇒r _ A VA [] _ (~[] _)))
... | done VB = done (VA V-⇒ VB)
progress⋆ (ƛ A) = done (V-ƛ A)
progress⋆ (A · B) with progress⋆ A
... | step p =
  step (contextRule ([] l· B) p (~l· A _ B [] (~[] A)) (~l· _ _ B [] (~[] _)))
... | done V with progress⋆ B
... | step p =
  step (contextRule (V ·r []) p (~·r B V B [] (~[] B)) (~·r _ V _ [] (~[] _)))
progress⋆ (.(ƛ _) · B) | done (V-ƛ A) | done VB = step (β-ƛ VB)
progress⋆ (con tcn) = done (V-con tcn)
```

## Determinism of Reduction:

A type is a value or it can make a step, but not both:

```
--notboth : (A : ∅ ⊢⋆ K) → ¬ (Value⋆ A × (Σ (∅ ⊢⋆ K) (A —→⋆_)))
```

Reduction is deterministic. There is only one possible reduction step
a type can make.

```
--det : (p : A —→⋆ B)(q : A —→⋆ B') → B ≡ B'
```
