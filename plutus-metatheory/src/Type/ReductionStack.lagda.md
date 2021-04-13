---
title: Type Reduction
layout: page
---

This is an experiment in using a stack of frames to present reduction.
It close to the CK machine in style. It doesn't seperate the beta-rule
out into a seperate relation. It probably should.

```
module Type.ReductionStack where
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

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong;subst;sym;trans)
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
## Stack

A stack is a sequence of frames. It allows us to specify a single hole
deep in a type or one can think of it as a path from the root of the
type to a single hole somewhere deep inside the type.

```
data Stack (K : Kind) : Kind → Set where
  ε   : Stack K K
  _,_ : Stack K J → Frame J I → Stack K I

data BackStack (K : Kind) : Kind → Set where
  ε   : BackStack K K
  _,_ : Frame K J → BackStack J I → BackStack K I
```

Analogously to frames we can close a stack by plugging in a type of
appropriate kind.

```
closeStack : Stack K J → ∅ ⊢⋆ J → ∅ ⊢⋆ K
closeStack ε       A = A
closeStack (s , f) A = closeStack s (closeFrame f A)
```

## Reduction

Reduction is intrinsically kind preserving. This doesn't require proof.

```
infix 2 _—→⋆_
infix 2 _—→s_
infix 2 _—↠s_

data _—→⋆_ : ∀{J} → (∅ ⊢⋆ J) → (∅ ⊢⋆ J) → Set where
  β-ƛ : Value⋆ B
        -------------------
      → ƛ A · B —→⋆ A [ B ]

data _—→s_ : ∀{J} → (∅ ⊢⋆ J) → (∅ ⊢⋆ J) → Set where
  stackRule : ∀{K K'} → (s : Stack K K')
    → ∀{A A' : ∅ ⊢⋆ K'} → A —→⋆ A'
    → {B B' : ∅ ⊢⋆ K}
    → B ≡ closeStack s A
    → B' ≡ closeStack s A'
      --------------------
    → B —→s B'
    -- ^ explicit equality proofs make pattern matching easier and this uglier
```

## Reflexive transitie closure of reduction

```
data _—↠s_ : (∅ ⊢⋆ J) → (∅ ⊢⋆ J) → Set where

  refl—↠s : --------
             A —↠s A

  trans—↠s : A —→s B
           → B —↠s C
             -------
           → A —↠s C
```

## Progress

An enumeration of possible outcomes of progress: a step or we hit a value.

```
data Progress⋆ (A : ∅ ⊢⋆ K) : Set where
  step : A —→s B
         -----------
       → Progress⋆ A
  done : Value⋆ A
         -----------
       → Progress⋆ A
```

The progress proof. For any type in the empty context we can make
progress. Note that there is no case for variables as there are no
variables in the empty context.

```
open import Data.Sum

variable K' : Kind

extendStack : Frame K' K → Stack K J → Stack K' J
extendStack f ε        = ε , f
extendStack f (s , f') = extendStack f s , f'

extendStack-lemma : (f : Frame K' K)(s : Stack K J)(A : ∅ ⊢⋆ J)
  → closeFrame f (closeStack s A) ≡ closeStack (extendStack f s) A
extendStack-lemma f ε        A = refl
extendStack-lemma f (s , f') A = extendStack-lemma f s (closeFrame f' A)


data Factorisation (M : ∅ ⊢⋆ K) : Set where
  fact : (s : Stack K J)
       → (L : ∅ ⊢⋆ I ⇒ J)
       → (N : ∅ ⊢⋆ I)
       → Value⋆ L
       → Value⋆ N
       → M ≡ closeStack s (L · N)
       → Factorisation M


factor : (M : ∅ ⊢⋆ K)
  → Value⋆ M
  ⊎ Factorisation M
factor (Π M)    = inj₁ (V-Π M)
factor (M ⇒ M') with factor M
... | inj₂ (fact s L N VL VN refl) =
  inj₂ (fact (extendStack (-⇒ M') s) L N VL VN (extendStack-lemma (-⇒ M') s (L · N)))
... | inj₁ VM with factor M'
... | inj₁ VM' = inj₁ (VM V-⇒ VM')
... | inj₂ (fact s L N VL VN refl) =
  inj₂ (fact (extendStack (VM ⇒-) s) L N VL VN (extendStack-lemma (VM ⇒-) s (L · N)))
factor (ƛ M)    = inj₁ (V-ƛ M)
factor (M · M') with factor M
... | inj₂ (fact s L N VL VN refl) =
  inj₂ (fact (extendStack (-· M') s) L N VL VN (extendStack-lemma (-· M') s (L · N)))
... | inj₁ VM with factor M'
... | inj₁ VM' = inj₂ (fact ε M M' VM VM' refl)
... | inj₂ (fact s L N VL VN refl) =
  inj₂ (fact (extendStack (VM ·-) s) L N VL VN (extendStack-lemma (VM ·-) s (L · N)))
factor (μ M M') with factor M
... | inj₂ (fact s L N VL VN refl) =
  inj₂ (fact (extendStack (μ- M') s) L N VL VN (extendStack-lemma (μ- M') s (L · N)))
... | inj₁ VM with factor M'
... | inj₁ VM' = inj₁ (V-μ VM VM')
... | inj₂ (fact s L N VL VN refl) =
  inj₂ (fact (extendStack (μ VM -) s) L N VL VN (extendStack-lemma (μ VM -) s (L · N)))
factor (con c) = inj₁ (V-con c)

closeStack-inj : ∀ (s s' : Stack K J) A → closeStack s A ≡ closeStack s' A → s ≡ s'
closeStack-inj s s' A p = {!!}

factor-unique : (M : ∅ ⊢⋆ K) → Value⋆ M ⊎ ∃ λ (f : Factorisation M) → ∀ (f' : Factorisation M) → f ≡ f' 
factor-unique (Π M)    = inj₁ (V-Π M)
factor-unique (M ⇒ M') with factor-unique M
... | inj₁ VM = {!!}
... | inj₂ (fact s L N VL VN refl , U) = inj₂ ((fact (extendStack (-⇒ M') s) L N VL VN (extendStack-lemma (-⇒ M') s (L · N))) , λ {(fact s' L' N' VL' VN' p') → {!extendStack-lemma (-⇒ M') s (L · N)!}})
factor-unique (ƛ M)    = {!!}
factor-unique (M · M') = {!!}
factor-unique (μ M M') = {!!}
factor-unique (con c)  = {!!}

progress⋆ : (A : ∅ ⊢⋆ K) → Progress⋆ A
progress⋆ A with factor A
... | inj₁ VA = done VA
... | inj₂ (fact s _ N (V-ƛ L) VN p) =
  step (stackRule s (β-ƛ VN) p refl)
```

## Determinism of Reduction:

A type is a value or it can make a step, but not both:

```
-- an application is not a value
-- this is provable by λ()
lem0 : (A : ∅ ⊢⋆ I ⇒ J)(B : ∅ ⊢⋆ I) → Value⋆ (A · B) → ⊥
lem0 A B ()

-- you can't plug a application into a frame and get a value
lem1 : (f : Frame K J)(A : ∅ ⊢⋆ J) → (Value⋆ A → ⊥)
  → Value⋆ (closeFrame f A) → ⊥
lem1 (-⇒ x) A ¬V (V V-⇒ W) = ¬V V
lem1 (x ⇒-) A ¬V (W V-⇒ V) = ¬V V
lem1 (μ- B) A ¬V (V-μ V W) = ¬V V
lem1 μ x -  A ¬V (V-μ W V) = ¬V V

-- if you plug something into a thing that becomes a value, it's a value
lem1' : (f : Frame K J)(A : ∅ ⊢⋆ J) → Value⋆ (closeFrame f A) → Value⋆ A
lem1' (-⇒ C) A (V V-⇒ W) = V
lem1' (C ⇒-) A (V V-⇒ W) = W
lem1' (μ- C) A (V-μ V W) = V
lem1' μ C -  A (V-μ V W) = W

lem2' : (s : Stack K J)(A : ∅ ⊢⋆ J) → Value⋆ (closeStack s A) → Value⋆ A
lem2' ε       A V = V
lem2' (s , f) A V = lem1' f A (lem2' s (closeFrame f A) V)

lem2 : (s : Stack K J)(A : ∅ ⊢⋆ J) → (Value⋆ A → ⊥)
  → Value⋆ (closeStack s A) → ⊥
lem2 ε       A ¬V V = ¬V V
lem2 (s , f) A ¬V W = lem2 s (closeFrame f A) (lem1 f A ¬V) W


--notboth : (A : ∅ ⊢⋆ K) → ¬ (Value⋆ A × (Σ (∅ ⊢⋆ K) (A —→s_)))
```

Reduction is deterministic. There is only one possible reduction step
a type can make.

```
-- det 
```
