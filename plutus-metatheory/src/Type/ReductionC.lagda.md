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

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong;subst)
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
... | step p = step (contextRule (μl [] B) p (~μl A A B [] (~[] A)) (~μl _ _ B [] (~[] _)))
... | done VA with progress⋆ B
... | step p = step (contextRule (μr VA []) p (~μr B A VA [] B (~[] B)) (~μr _ A VA [] _ (~[] _)))
... | done VB = done (V-μ VA VB)
progress⋆ (Π A) = done (V-Π A)
progress⋆ (A ⇒ B) with progress⋆ A
... | step p = step (contextRule ([] l⇒ B) p (~l⇒ A A B [] (~[] A)) (~l⇒ _ _ _ [] (~[] _)))
... | done VA with progress⋆ B
... | step q = step (contextRule (VA ⇒r []) q (~⇒r B _ VA [] B (~[] B)) (~⇒r _ A VA [] _ (~[] _)))
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
lem0 : ∀ A B (E : EvalCtx K J) → B ~ E ⟦ A ⟧ → Value⋆ B → Value⋆ A
lem0 A .A [] (~[] .A) V = V
lem0 A .(_ · B) (x ·r E) (~·r .A .x B .E p) ()
lem0 A .(A₁ · x) (E l· x) (~l· .A A₁ .x .E p) ()
lem0 A .(_ ⇒ B) (x ⇒r E) (~⇒r .A _ .x .E B p) (V V-⇒ W) = lem0 A B E p W
lem0 A .(A₁ ⇒ x) (E l⇒ x) (~l⇒ .A A₁ .x .E p) (V V-⇒ W) = lem0 A _ E p V
lem0 A .(μ _ B) (μr x E) (~μr .A _ .x .E B p) (V-μ V W) = lem0 A B E p W
lem0 A .(μ A₁ B₁) (μl E B₁) (~μl .A A₁ .B₁ .E p) (V-μ V W) = lem0 A _ E p V

notboth : (A : ∅ ⊢⋆ K) → ¬ (Value⋆ A × (Σ (∅ ⊢⋆ K) (A —→⋆_)))
notboth A (V , A' , contextRule [] p (~[] .A) (~[] .A')) = notboth A (V , A' , p)
notboth .(_ · B) (() , .(_ · B₁) , contextRule (x₂ ·r E) p (~·r _ .x₂ B .E x) (~·r _ .x₂ B₁ .E x₁))
notboth .(A · x₂) (() , .(A₁ · x₂) , contextRule (E l· x₂) p (~l· _ A .x₂ .E x) (~l· _ A₁ .x₂ .E x₁))
notboth .(_ ⇒ B) ((V V-⇒ W) , .(_ ⇒ B₁) , contextRule (x₂ ⇒r E) p (~⇒r _ _ .x₂ .E B x) (~⇒r _ _ .x₂ .E B₁ x₁)) = notboth _ (W , _ , contextRule E p x x₁)
notboth .(A ⇒ x₂) (V V-⇒ W , .(A₁ ⇒ x₂) , contextRule (E l⇒ x₂) p (~l⇒ _ A .x₂ .E x) (~l⇒ _ A₁ .x₂ .E x₁)) = notboth _ (V , _ , contextRule E p x x₁)
notboth .(μ _ B) (V-μ V W , .(μ _ B₁) , contextRule (μr x₂ E) p (~μr _ _ .x₂ .E B x) (~μr _ _ .x₂ .E B₁ x₁)) = notboth _ (W , _ , contextRule E p x x₁)
notboth .(μ A B) (V-μ V W , .(μ A₁ B) , contextRule (μl E B) p (~μl _ A .B .E x) (~μl _ A₁ .B .E x₁)) = notboth _ (V , _ , contextRule E p x x₁)
```

This is not as precisely deterministic as, e.g., we can have beta at
the top level or we can have beta inside the empty evaluation
context. Different rules, same answer. So, we have B ≡ B' but not p ≡ q

```
-- if something reduces in an eval ctx then it should be in the only
-- possible place


det : (p : A —→⋆ B)(q : A —→⋆ B') → B ≡ B'
det (contextRule [] p (~[] _) (~[] _)) q = det p q
det (contextRule (x₄ ·r E) p x x₁) (contextRule [] q (~[] _) (~[] _)) =
  det (contextRule _ p x x₁) q
det (contextRule (x₄ ·r E) p (~·r _ .x₄ B .E x) (~·r _ .x₄ B₁ .E x₁)) (contextRule (x₅ ·r E') q (~·r _ .x₅ .B .E' x₂) (~·r _ .x₅ B₂ .E' x₃)) =
  cong (_ ·_) (det (contextRule E p x x₁) (contextRule E' q x₂ x₃))
det (contextRule (x₄ ·r E) p (~·r _ .x₄ B .E x) (~·r _ .x₄ B₁ .E x₁)) (contextRule (E' l· .B) q (~l· _ _ .B .E' x₂) (~l· _ A .B .E' x₃)) =
  ⊥-elim (notboth _ (lem0 _ _ _ x₂ x₄ , _ , q))
det (contextRule (x₄ ·r E) p (~·r _ .x₄ B .E x) (~·r _ .x₄ B₁ .E x₁)) (contextRule (x₅ ⇒r E') q () x₃)
det (contextRule (x₄ ·r E) p (~·r _ .x₄ B .E x) (~·r _ .x₄ B₁ .E x₁)) (contextRule (E' l⇒ x₅) q () x₃)
det (contextRule (x₄ ·r E) p (~·r _ .x₄ B .E x) (~·r _ .x₄ B₁ .E x₁)) (contextRule (μr x₅ E') q () x₃)
det (contextRule (x₄ ·r E) p (~·r _ .x₄ B₁ .E x) (~·r _ .x₄ B₂ .E x₁)) (contextRule (μl E' B) q () x₃)
det C@(contextRule (E l· x₄) p x x₁) (contextRule [] q (~[] _) (~[] _)) =
  det C q
det (contextRule (E l· x₄) p (~l· _ A .x₄ .E x) (~l· _ A₁ .x₄ .E x₁)) (contextRule (x₅ ·r E') q (~·r _ .x₅ .x₄ .E' x₂) (~·r _ .x₅ B .E' x₃)) =
  ⊥-elim (notboth _ (lem0 _ _ _ x x₅ , _ , p))
det (contextRule (E l· x₄) p (~l· _ A .x₄ .E x) (~l· _ A₁ .x₄ .E x₁)) (contextRule (E' l· .x₄) q (~l· _ .A .x₄ .E' x₂) (~l· _ A₂ .x₄ .E' x₃)) =
  cong (_· _) (det (contextRule E p x x₁) (contextRule E' q x₂ x₃))
det (contextRule (E l· x₄) p (~l· _ A .x₄ .E x) (~l· _ A₁ .x₄ .E x₁)) (contextRule (x₅ ⇒r E') q () x₃)
det (contextRule (E l· x₄) p (~l· _ A .x₄ .E x) (~l· _ A₁ .x₄ .E x₁)) (contextRule (E' l⇒ x₅) q () x₃)
det (contextRule (E l· x₄) p (~l· _ A .x₄ .E x) (~l· _ A₁ .x₄ .E x₁)) (contextRule (μr x₅ E') q () x₃)
det (contextRule (E l· x₄) p (~l· _ A .x₄ .E x) (~l· _ A₁ .x₄ .E x₁)) (contextRule (μl E' B) q () x₃)
det C@(contextRule (x₄ ⇒r E) p x x₁) (contextRule [] q (~[] _) (~[] _)) =
  det C q 
det (contextRule (x₄ ⇒r E) p (~⇒r _ _ .x₄ .E B x) (~⇒r _ _ .x₄ .E B₁ x₁)) (contextRule (x₅ ·r E') q () x₃)
det (contextRule (x₄ ⇒r E) p (~⇒r _ _ .x₄ .E B x) (~⇒r _ _ .x₄ .E B₁ x₁)) (contextRule (E' l· x₅) q () x₃)
det (contextRule (x₄ ⇒r E) p (~⇒r _ _ .x₄ .E B x) (~⇒r _ _ .x₄ .E B₁ x₁)) (contextRule (x₅ ⇒r E') q (~⇒r _ _ .x₅ .E' .B x₂) (~⇒r _ _ .x₅ .E' B₂ x₃)) =
   cong (_ ⇒_) (det (contextRule E p x x₁) (contextRule E' q x₂ x₃))
det (contextRule (x₄ ⇒r E) p (~⇒r _ _ .x₄ .E B x) (~⇒r _ _ .x₄ .E B₁ x₁)) (contextRule (E' l⇒ .B) q (~l⇒ _ _ .B .E' x₂) (~l⇒ _ A .B .E' x₃)) =
  ⊥-elim (notboth _ (lem0 _ _ _ x₂ x₄ , _ , q))
det (contextRule (x₄ ⇒r E) p (~⇒r _ _ .x₄ .E B x) (~⇒r _ _ .x₄ .E B₁ x₁)) (contextRule (μr x₅ E') q () x₃)
det (contextRule (x₄ ⇒r E) p (~⇒r _ _ .x₄ .E B₁ x) (~⇒r _ _ .x₄ .E B₂ x₁)) (contextRule (μl E' B) q () x₃)
det C@(contextRule (E l⇒ x₄) p x x₁) (contextRule [] q (~[] _) (~[] _)) =
  det C q
det (contextRule (E l⇒ x₄) p (~l⇒ _ A .x₄ .E x) (~l⇒ _ A₁ .x₄ .E x₁)) (contextRule (x₅ ·r E') q () x₃)
det (contextRule (E l⇒ x₄) p (~l⇒ _ A .x₄ .E x) (~l⇒ _ A₁ .x₄ .E x₁)) (contextRule (E' l· x₅) q () x₃)
det (contextRule (E l⇒ x₄) p (~l⇒ _ A .x₄ .E x) (~l⇒ _ A₁ .x₄ .E x₁)) (contextRule (x₅ ⇒r E') q (~⇒r _ .A .x₅ .E' .x₄ x₂) (~⇒r _ .A .x₅ .E' B x₃)) =
  ⊥-elim (notboth _ (lem0 _ _ _ x x₅ , _ , p))
det (contextRule (E l⇒ x₄) p (~l⇒ _ A .x₄ .E x) (~l⇒ _ A₁ .x₄ .E x₁)) (contextRule (E' l⇒ .x₄) q (~l⇒ _ .A .x₄ .E' x₂) (~l⇒ _ A₂ .x₄ .E' x₃)) =
  cong (_⇒ _) (det (contextRule E p x x₁) (contextRule E' q x₂ x₃))
det (contextRule (E l⇒ x₄) p (~l⇒ _ A .x₄ .E x) (~l⇒ _ A₁ .x₄ .E x₁)) (contextRule (μr x₅ E') q () x₃)
det (contextRule (E l⇒ x₄) p (~l⇒ _ A .x₄ .E x) (~l⇒ _ A₁ .x₄ .E x₁)) (contextRule (μl E' B) q () x₃)
det C@(contextRule (μr x₄ E) p x x₁) (contextRule [] q (~[] _) (~[] _)) =
  det C q
det (contextRule (μr x₄ E) p (~μr _ _ .x₄ .E B x) (~μr _ _ .x₄ .E B₁ x₁)) (contextRule (x₅ ·r E') q () x₃)
det (contextRule (μr x₄ E) p (~μr _ _ .x₄ .E B x) (~μr _ _ .x₄ .E B₁ x₁)) (contextRule (E' l· x₅) q () x₃)
det (contextRule (μr x₄ E) p (~μr _ _ .x₄ .E B x) (~μr _ _ .x₄ .E B₁ x₁)) (contextRule (x₅ ⇒r E') q () x₃)
det (contextRule (μr x₄ E) p (~μr _ _ .x₄ .E B x) (~μr _ _ .x₄ .E B₁ x₁)) (contextRule (E' l⇒ x₅) q () x₃)
det (contextRule (μr x₄ E) p (~μr _ _ .x₄ .E B x) (~μr _ _ .x₄ .E B₁ x₁)) (contextRule (μr x₅ E') q (~μr _ _ .x₅ .E' .B x₂) (~μr _ _ .x₅ .E' B₂ x₃)) =
  cong (μ _) (det (contextRule E p x x₁) (contextRule E' q x₂ x₃))
det (contextRule (μr x₄ E) p (~μr _ _ .x₄ .E B x) (~μr _ _ .x₄ .E B₁ x₁)) (contextRule (μl E' B) q (~μl _ _ .B .E' x₂) (~μl _ A .B .E' x₃)) =
  ⊥-elim (notboth _ (lem0 _ _ _ x₂ x₄ , _ , q))
det C@(contextRule (μl E B) p x x₁) (contextRule [] q (~[] _) (~[] _)) = det C q
det (contextRule (μl E B) p (~μl _ A .B .E x) (~μl _ A₁ .B .E x₁)) (contextRule (x₄ ·r E') q () x₃)
det (contextRule (μl E B) p (~μl _ A .B .E x) (~μl _ A₁ .B .E x₁)) (contextRule (E' l· x₄) q () x₃)
det (contextRule (μl E B) p (~μl _ A .B .E x) (~μl _ A₁ .B .E x₁)) (contextRule (x₄ ⇒r E') q () x₃)
det (contextRule (μl E B) p (~μl _ A .B .E x) (~μl _ A₁ .B .E x₁)) (contextRule (E' l⇒ x₄) q () x₃)
det (contextRule (μl E B) p (~μl _ A .B .E x) (~μl _ A₁ .B .E x₁)) (contextRule (μr x₄ E') q (~μr _ .A .x₄ .E' .B x₂) (~μr _ .A .x₄ .E' B₁ x₃)) =
  ⊥-elim (notboth _ (lem0 _ _ _ x x₄ , _ , p))
det (contextRule (μl E B) p (~μl _ A .B .E x) (~μl _ A₁ .B .E x₁)) (contextRule (μl E' .B) q (~μl _ .A .B .E' x₂) (~μl _ A₂ .B .E' x₃)) =
  cong (λ A → μ A _) (det (contextRule E p x x₁) (contextRule E' q x₂ x₃))
det (contextRule (x₃ ·r E) p (~·r _ .x₃ _ .E x) (~·r _ .x₃ B .E x₁)) (β-ƛ x₂) =
 ⊥-elim (notboth _ (lem0 _ _ _ x x₂ , _ , p))
det (contextRule (E l· x₃) p (~l· _ .(ƛ _) .x₃ .E x) (~l· _ A .x₃ .E x₁)) (β-ƛ x₂) = ⊥-elim (notboth _ (lem0 _ _ _ x (V-ƛ _) , _ , p))
det (β-ƛ x) (contextRule [] q (~[] .(ƛ _ · _)) (~[] _)) = det (β-ƛ x) q
det (β-ƛ x) (contextRule (x₃ ·r E) q (~·r _ .x₃ _ .E x₁) (~·r _ .x₃ B .E x₂)) = ⊥-elim (notboth _ (lem0 _ _ _ x₁ x , _ , q))
det (β-ƛ x) (contextRule (E l· x₃) q (~l· _ .(ƛ _) .x₃ _ x₁) (~l· _ A .x₃ _ x₂)) = ⊥-elim (notboth _ (lem0 _ _ _ x₁ (V-ƛ _) , _ , q))
det (β-ƛ x) (β-ƛ x₁) = refl
```
