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
open import Data.Product hiding (∃!)
open import Data.Empty

open import Relation.Binary.PropositionalEquality
  using (_≡_;refl;cong;cong₂;subst;trans;sym;inspect) renaming ([_] to blah)
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


-- this is a bit like substitution
closeEvalCtx : EvalCtx K J → ∅ ⊢⋆ J → ∅ ⊢⋆ K
closeEvalCtx []       C = C
closeEvalCtx (V ·r E) C = discharge V · closeEvalCtx E C
closeEvalCtx (E l· B) C = closeEvalCtx E C · B
closeEvalCtx (V ⇒r E) C = discharge V ⇒ closeEvalCtx E C
closeEvalCtx (E l⇒ B) C = closeEvalCtx E C ⇒ B
closeEvalCtx (μr V E) C = μ (discharge V) (closeEvalCtx E C)
closeEvalCtx (μl E B) C = μ (closeEvalCtx E C) B

-- the most direct way to define composition
-- by induction on the first arg
compEvalCtx : EvalCtx K J → EvalCtx J I → EvalCtx K I
compEvalCtx []       E' = E'
compEvalCtx (V ·r E) E' = V ·r compEvalCtx E E'
compEvalCtx (E l· B) E' = compEvalCtx E E' l· B
compEvalCtx (V ⇒r E) E' = V ⇒r compEvalCtx E E'
compEvalCtx (E l⇒ B) E' = compEvalCtx E E' l⇒ B
compEvalCtx (μr V E) E' = μr V (compEvalCtx E E')
compEvalCtx (μl E B) E' = μl (compEvalCtx E E') B

-- some laws about closing and composition

-- monoid laws for composition
comp-idl : (E : EvalCtx K J) → compEvalCtx [] E ≡ E
comp-idl E = refl

comp-idr : (E : EvalCtx K J) → compEvalCtx E [] ≡ E
comp-idr []       = refl
comp-idr (A ·r E) = cong (A ·r_) (comp-idr E)
comp-idr (E l· B) = cong (_l· B) (comp-idr E)
comp-idr (A ⇒r E) = cong (A ⇒r_) (comp-idr E)
comp-idr (E l⇒ B) = cong (_l⇒ B) (comp-idr E)
comp-idr (μr A E) = cong (μr A) (comp-idr E)
comp-idr (μl E B) = cong (λ E → μl E B) (comp-idr E)

variable H : Kind

comp-assoc : (E : EvalCtx K J)(E' : EvalCtx J I)(E'' : EvalCtx I H)
           → compEvalCtx E (compEvalCtx E' E'')
           ≡ compEvalCtx (compEvalCtx E E') E''
comp-assoc []       E' E'' = refl
comp-assoc (A ·r E) E' E'' = cong (A ·r_) (comp-assoc E E' E'')
comp-assoc (E l· B) E' E'' = cong (_l· B) (comp-assoc E E' E'')
comp-assoc (A ⇒r E) E' E'' = cong (A ⇒r_) (comp-assoc E E' E'')
comp-assoc (E l⇒ B) E' E'' = cong (_l⇒ B) (comp-assoc E E' E'')
comp-assoc (μr A E) E' E'' = cong (μr A) (comp-assoc E E' E'')
comp-assoc (μl E B) E' E'' = cong (λ E → μl E B) (comp-assoc E E' E'')

-- functor laws for close
close-id : (A : ∅ ⊢⋆ K) → closeEvalCtx [] A ≡ A
close-id A = refl

close-comp : (E : EvalCtx K J)(E' : EvalCtx J I)(A : ∅ ⊢⋆ I)
           → closeEvalCtx (compEvalCtx E E') A
           ≡ closeEvalCtx E (closeEvalCtx E' A)
close-comp []       E' A = refl
close-comp (V ·r E) E' A = cong (discharge V ·_) (close-comp E E' A)
close-comp (E l· B) E' A = cong (_· B) (close-comp E E' A)
close-comp (V ⇒r E) E' A = cong (discharge V ⇒_) (close-comp E E' A)
close-comp (E l⇒ B) E' A = cong (_⇒ B) (close-comp E E' A)
close-comp (μr V E) E' A = cong (μ (discharge V)) (close-comp E E' A)
close-comp (μl E B) E' A = cong (λ E → μ E B) (close-comp E E' A)
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

extendEvalCtx : (E : EvalCtx K J)(F : Frame J I) → EvalCtx K I
extendEvalCtx [] (-· B)  = [] l· B
extendEvalCtx [] (V ·-)  = V ·r []
extendEvalCtx [] (-⇒ B)  = [] l⇒ B
extendEvalCtx [] (V ⇒-)  = V ⇒r []
extendEvalCtx [] (μ- B)  = μl [] B
extendEvalCtx [] μ V -   = μr V []
extendEvalCtx (V ·r E) F = V ·r extendEvalCtx E F
extendEvalCtx (E l· B) F = extendEvalCtx E F l· B
extendEvalCtx (V ⇒r E) F = V ⇒r extendEvalCtx E F
extendEvalCtx (E l⇒ B) F = extendEvalCtx E F l⇒ B
extendEvalCtx (μr V E) F = μr V (extendEvalCtx E F)
extendEvalCtx (μl E B) F = μl (extendEvalCtx E F) B

closeEF : (E : EvalCtx K J)(F : Frame J I)(A : ∅ ⊢⋆ I)
     → closeEvalCtx (extendEvalCtx E F) A
     ≡ closeEvalCtx E (closeFrame F A)
closeEF [] (-· B) A = refl
closeEF [] (V ·-) A = refl
closeEF [] (-⇒ B) A = refl
closeEF [] (V ⇒-) A = refl
closeEF [] (μ- B) A = refl
closeEF [] μ V -  A = refl
closeEF (V ·r E) F A = cong (_ ·_) (closeEF E F A)
closeEF (E l· B) F A = cong (_· _) (closeEF E F A)
closeEF (V ⇒r E) F A = cong (_ ⇒_) (closeEF E F A)
closeEF (E l⇒ B) F A = cong (_⇒ _) (closeEF E F A)
closeEF (μr V E) F A = cong (μ _) (closeEF E F A)
closeEF (μl E B) F A = cong (λ A → μ A _) (closeEF E F A)

-- there should be a law for comp and e,f too...

-- composition can also be defined by induction on E'
compEvalCtx' : EvalCtx K J → EvalCtx J I → EvalCtx K I
compEvalCtx' E []        = E
compEvalCtx' E (V ·r E') = compEvalCtx' (extendEvalCtx E (V ·-)) E'
compEvalCtx' E (E' l· B) = compEvalCtx' (extendEvalCtx E (-· B)) E'
compEvalCtx' E (V ⇒r E') = compEvalCtx' (extendEvalCtx E (V ⇒-)) E'
compEvalCtx' E (E' l⇒ B) = compEvalCtx' (extendEvalCtx E (-⇒ B)) E'
compEvalCtx' E (μr V E') = compEvalCtx' (extendEvalCtx E (μ V -)) E'
compEvalCtx' E (μl E' B) = compEvalCtx' (extendEvalCtx E (μ- B)) E'

-- these are properties that hold definitionally of compEvalCtx
compEvalCtx'-·r : ∀(E : EvalCtx K J)(E' : EvalCtx J I)
                  {A : ∅ ⊢⋆ K ⇒ H}(V : Value⋆ A)
                → V ·r compEvalCtx' E E' ≡ compEvalCtx' (V ·r E) E'
compEvalCtx'-·r E []        V = refl
compEvalCtx'-·r E (x ·r E') V = compEvalCtx'-·r _ E' V
compEvalCtx'-·r E (E' l· x) V = compEvalCtx'-·r _ E' V
compEvalCtx'-·r E (x ⇒r E') V = compEvalCtx'-·r _ E' V
compEvalCtx'-·r E (E' l⇒ x) V = compEvalCtx'-·r _ E' V
compEvalCtx'-·r E (μr x E') V = compEvalCtx'-·r _ E' V
compEvalCtx'-·r E (μl E' B) V = compEvalCtx'-·r _ E' V

compEvalCtx'-l· : ∀(E : EvalCtx (K ⇒ H) J)(E' : EvalCtx J I) B
                → compEvalCtx' E E' l· B ≡ compEvalCtx' (E l· B) E'
compEvalCtx'-l· E []        C = refl
compEvalCtx'-l· E (V ·r E') C = compEvalCtx'-l· _ E' C
compEvalCtx'-l· E (E' l· B) C = compEvalCtx'-l· _ E' C
compEvalCtx'-l· E (V ⇒r E') C = compEvalCtx'-l· _ E' C
compEvalCtx'-l· E (E' l⇒ B) C = compEvalCtx'-l· _ E' C
compEvalCtx'-l· E (μr V E') C = compEvalCtx'-l· _ E' C
compEvalCtx'-l· E (μl E' B) C = compEvalCtx'-l· _ E' C

compEvalCtx'-⇒r : ∀(E : EvalCtx * J)(E' : EvalCtx J I)
                  {A : ∅ ⊢⋆ *}(V : Value⋆ A)
                → V ⇒r compEvalCtx' E E' ≡ compEvalCtx' (V ⇒r E) E'
compEvalCtx'-⇒r E []        V = refl
compEvalCtx'-⇒r E (x ·r E') V = compEvalCtx'-⇒r _ E' V
compEvalCtx'-⇒r E (E' l· x) V = compEvalCtx'-⇒r _ E' V
compEvalCtx'-⇒r E (x ⇒r E') V = compEvalCtx'-⇒r _ E' V
compEvalCtx'-⇒r E (E' l⇒ x) V = compEvalCtx'-⇒r _ E' V
compEvalCtx'-⇒r E (μr x E') V = compEvalCtx'-⇒r _ E' V
compEvalCtx'-⇒r E (μl E' B) V = compEvalCtx'-⇒r _ E' V

compEvalCtx'-l⇒ : ∀(E : EvalCtx * J)(E' : EvalCtx J I) B
                → compEvalCtx' E E' l⇒ B ≡ compEvalCtx' (E l⇒ B) E'
compEvalCtx'-l⇒ E []        C = refl
compEvalCtx'-l⇒ E (V ·r E') C = compEvalCtx'-l⇒ _ E' C
compEvalCtx'-l⇒ E (E' l· B) C = compEvalCtx'-l⇒ _ E' C
compEvalCtx'-l⇒ E (V ⇒r E') C = compEvalCtx'-l⇒ _ E' C
compEvalCtx'-l⇒ E (E' l⇒ B) C = compEvalCtx'-l⇒ _ E' C
compEvalCtx'-l⇒ E (μr V E') C = compEvalCtx'-l⇒ _ E' C
compEvalCtx'-l⇒ E (μl E' B) C = compEvalCtx'-l⇒ _ E' C

compEvalCtx'-μr : ∀(E : EvalCtx K J)(E' : EvalCtx J I)
                  {A : ∅ ⊢⋆ _}(V : Value⋆ A)
                → μr V (compEvalCtx' E E') ≡ compEvalCtx' (μr V E) E'
compEvalCtx'-μr E []        V = refl
compEvalCtx'-μr E (x ·r E') V = compEvalCtx'-μr _ E' V
compEvalCtx'-μr E (E' l· x) V = compEvalCtx'-μr _ E' V
compEvalCtx'-μr E (x ⇒r E') V = compEvalCtx'-μr _ E' V
compEvalCtx'-μr E (E' l⇒ x) V = compEvalCtx'-μr _ E' V
compEvalCtx'-μr E (μr x E') V = compEvalCtx'-μr _ E' V
compEvalCtx'-μr E (μl E' B) V = compEvalCtx'-μr _ E' V 

compEvalCtx'-lμ : ∀(E : EvalCtx _ J)(E' : EvalCtx J I)(B : ∅ ⊢⋆ K)
                → μl (compEvalCtx' E E') B ≡ compEvalCtx' (μl E B) E'
compEvalCtx'-lμ E []        C = refl
compEvalCtx'-lμ E (V ·r E') C = compEvalCtx'-lμ _ E' C
compEvalCtx'-lμ E (E' l· B) C = compEvalCtx'-lμ _ E' C
compEvalCtx'-lμ E (V ⇒r E') C = compEvalCtx'-lμ _ E' C
compEvalCtx'-lμ E (E' l⇒ B) C = compEvalCtx'-lμ _ E' C
compEvalCtx'-lμ E (μr V E') C = compEvalCtx'-lμ _ E' C
compEvalCtx'-lμ E (μl E' B) C = compEvalCtx'-lμ _ E' C


compEvalCtx'-[] : (E' : EvalCtx K J) → E' ≡ compEvalCtx' [] E'
compEvalCtx'-[] [] = refl
compEvalCtx'-[] (V ·r E') =
  trans (cong (V ·r_) (compEvalCtx'-[] E')) (compEvalCtx'-·r [] E' V)
compEvalCtx'-[] (E' l· B) =
  trans (cong (_l· B) (compEvalCtx'-[] E')) (compEvalCtx'-l· [] E' B)
compEvalCtx'-[] (V ⇒r E') =
  trans (cong (V ⇒r_) (compEvalCtx'-[] E')) (compEvalCtx'-⇒r [] E' V)
compEvalCtx'-[] (E' l⇒ B) =
  trans (cong (_l⇒ B) (compEvalCtx'-[] E')) (compEvalCtx'-l⇒ [] E' B)
compEvalCtx'-[] (μr V E') =
  trans (cong (μr V) (compEvalCtx'-[] E')) (compEvalCtx'-μr [] E' V)
compEvalCtx'-[] (μl E' B) =
  trans (cong (λ E → μl E B) (compEvalCtx'-[] E')) (compEvalCtx'-lμ [] E' B)

compEvalCtx-eq : (E : EvalCtx K J)(E' : EvalCtx J I)
               → compEvalCtx E E' ≡ compEvalCtx' E E'
compEvalCtx-eq [] E' = compEvalCtx'-[] E'
compEvalCtx-eq (V ·r E) E' =
  trans (cong (V ·r_) (compEvalCtx-eq E E')) (compEvalCtx'-·r E E' V)
compEvalCtx-eq (E l· B) E' =
  trans (cong (_l· B) (compEvalCtx-eq E E')) (compEvalCtx'-l· E E' B)
compEvalCtx-eq (V ⇒r E) E' =
  trans (cong (V ⇒r_) (compEvalCtx-eq E E')) (compEvalCtx'-⇒r E E' V)
compEvalCtx-eq (E l⇒ B) E' =
  trans (cong (_l⇒ B) (compEvalCtx-eq E E')) (compEvalCtx'-l⇒ E E' B)
compEvalCtx-eq (μr V E) E' =
  trans (cong (μr V) (compEvalCtx-eq E E')) (compEvalCtx'-μr E E' V)
compEvalCtx-eq (μl E B) E' =
  trans (cong (λ E → μl E B) (compEvalCtx-eq E E')) (compEvalCtx'-lμ E E' B)

-- because compEvalCtx = compEvalCtx', it is also a monoid
comp'-idl : (E : EvalCtx K J) → compEvalCtx' [] E ≡ E
comp'-idl E = sym (compEvalCtx-eq [] E)

comp'-idr : (E : EvalCtx K J) → compEvalCtx' E [] ≡ E
comp'-idr E = refl

comp'-assoc : (E : EvalCtx K J)(E' : EvalCtx J I)(E'' : EvalCtx I H)
           → compEvalCtx' E (compEvalCtx' E' E'')
           ≡ compEvalCtx' (compEvalCtx' E E') E''
comp'-assoc E E' E'' = trans
  (sym (compEvalCtx-eq E (compEvalCtx' E' E'')))
  (trans (cong (compEvalCtx E) (sym (compEvalCtx-eq E' E'')))
         (trans (comp-assoc E E' E'')
                (trans (compEvalCtx-eq (compEvalCtx E E') E'')
                       (cong (λ E → compEvalCtx' E E'')
                             (compEvalCtx-eq E E')))))
```


## Reduction

Reduction is intrinsically kind preserving. This doesn't require proof.

```
infix 2 _—→⋆_
infix 2 _—→E_
infix 2 _—↠E_

data _—→⋆_ : ∀{J} → (∅ ⊢⋆ J) → (∅ ⊢⋆ J) → Set where
  β-ƛ : Value⋆ B
        -------------------
      → ƛ A · B —→⋆ A [ B ]

data _—→E_ : ∀{J} → (∅ ⊢⋆ J) → (∅ ⊢⋆ J) → Set where
  contextRule : ∀{K K'}
    → (E : EvalCtx K K')
    → ∀{A A' : ∅ ⊢⋆ K'}
    → A —→⋆ A'
    → {B B' : ∅ ⊢⋆ K}
    → B  ≡ closeEvalCtx E A
    → B' ≡ closeEvalCtx E A'
      --------------------
    → B —→E B'
    -- ^ explicit equality proofs make pattern matching easier and this uglier

```

## Reflexive transitie closure of reduction

```
data _—↠E_ : (∅ ⊢⋆ J) → (∅ ⊢⋆ J) → Set where

  refl—↠E : --------
             A —↠E A

  trans—↠E : A —→E B
           → B —↠E C
             -------
           → A —↠E C
```

## Progress

An enumeration of possible outcomes of progress: a step or we hit a value.

```
data Progress⋆ (A : ∅ ⊢⋆ K) : Set where
  step : A —→E B
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
... | step (contextRule E p refl refl) =
  step (contextRule (μl E B) p refl refl)
... | done VA with progress⋆ B
... | step (contextRule E p refl refl) =
  step (contextRule (μr VA E) p refl refl)
... | done VB = done (V-μ VA VB)
progress⋆ (Π A) = done (V-Π A)
progress⋆ (A ⇒ B) with progress⋆ A
... | step (contextRule E p refl refl) =
  step (contextRule (E l⇒ B) p refl refl)
... | done VA with progress⋆ B
... | step (contextRule E p refl refl) =
  step (contextRule (VA ⇒r E) p refl refl)
... | done VB = done (VA V-⇒ VB)
progress⋆ (ƛ A) = done (V-ƛ A)
progress⋆ (A · B) with progress⋆ A
... | step (contextRule E p refl refl) =
  step (contextRule (E l· B) p refl refl)
... | done V with progress⋆ B
... | step (contextRule E p refl refl) =
  step (contextRule (V ·r E) p refl refl)
progress⋆ (.(ƛ _) · B) | done (V-ƛ A) | done VB =
  step (contextRule [] (β-ƛ VB) refl refl)
progress⋆ (con tcn) = done (V-con tcn)
```

## Determinism of Reduction:

A type is a value or it can make a step, but not both:

```
lem0 : ∀ A (E : EvalCtx K J) → Value⋆ (closeEvalCtx E A) → Value⋆ A
lem0 A []       V          = V
lem0 A (_ ⇒r E) (W V-⇒ W') = lem0 A E W'
lem0 A (E l⇒ B) (W V-⇒ W') = lem0 A E W
lem0 A (μr _ E) (V-μ W W') = lem0 A E W'
lem0 A (μl E B) (V-μ W W') = lem0 A E W

lemV· : ∀{A : ∅ ⊢⋆ K ⇒ J}{B} → Value⋆ (A · B) → ⊥
lemV· ()

notboth : (A : ∅ ⊢⋆ K) → ¬ (Value⋆ A × (Σ (∅ ⊢⋆ K) (A —→E_)))
notboth .(ƛ _ · _) (() , _ , contextRule [] (β-ƛ x) refl refl)
notboth _ (() , _ , contextRule (V ·r E) p refl refl)
notboth _ (() , _ , contextRule (E l· B) p refl refl)
notboth _ ((V V-⇒ W) , _ , contextRule (_ ⇒r E) p refl refl) =
  notboth _ (W , _ , contextRule E p refl refl)
notboth _ ((V V-⇒ W) , _ , contextRule (E l⇒ B) p refl refl) =
  notboth _ (V , _ , contextRule E p refl refl)
notboth _ (V-μ V W , _ , contextRule (μr _ E) p refl refl) =
  notboth _ (W , _ , contextRule E p refl refl)
notboth _ (V-μ V W , _ , contextRule (μl E B) p refl refl) =
  notboth _ (V , _ , contextRule E p refl refl)
```

This is not as precisely deterministic as, e.g., we can have beta at
the top level or we can have beta inside the empty evaluation
context. Different rules, same answer. So, we have B ≡ B' but not p ≡ q

```
variable K' : Kind

inv·l : ∀ A A' (B : ∅ ⊢⋆ K)(B' : ∅ ⊢⋆ K')
  → A · B ≡ A' · B' → Σ (K' ⇒ J ≡ K ⇒ J) λ p → A ≡ subst (∅ ⊢⋆_) p A'
inv·l A .A B .B refl = refl , refl

inv·r : ∀ (A : ∅ ⊢⋆ K ⇒ J) A' (B : ∅ ⊢⋆ K)(B' : ∅ ⊢⋆ K')
  → A · B ≡ A' · B' → Σ (K' ≡ K) λ p → B ≡ subst (∅ ⊢⋆_) p B'
inv·r A .A B .B refl = refl , refl

open import Data.Sum
lemma51 : (M : ∅ ⊢⋆ K)
  → Value⋆ M
  ⊎ Σ Kind λ J →
    Σ (EvalCtx K J) λ E →
    Σ Kind λ I → 
    Σ (∅ ⊢⋆ I ⇒ J)  λ L →
    Σ (∅ ⊢⋆ I)      λ N →
      Value⋆ L
    × Value⋆ N
    × M ≡ closeEvalCtx E (L · N)
lemma51 (Π M)    = inj₁ (V-Π M)
lemma51 (M ⇒ M') with lemma51 M
... | inj₂ (J , E , I , L , N , VL , VN , p) =
  inj₂ (J , E l⇒ M' , I , L , N , VL , VN , cong (_⇒ M') p)
... | inj₁ VM with lemma51 M'
... | inj₂ (J , E , I , L , N , VL , VN , p) =
  inj₂ (J , VM ⇒r E , I , L , N , VL , VN , cong (M ⇒_) p)
... | inj₁ VM' = inj₁ (VM V-⇒ VM')
lemma51 (ƛ M)    = inj₁ (V-ƛ M)
lemma51 (M · M') with lemma51 M
... | inj₂ (J , E , I , L , N , VL , VN , p) =
  inj₂ (J , E l· M' , I , L , N , VL , VN , cong (_· M') p)
... | inj₁ VM with lemma51 M'
... | inj₂ (J , E , I , L , N , VL , VN , p) =
  inj₂ (J , VM ·r E , I , L , N , VL , VN , cong (M ·_) p)
... | inj₁ VM' = inj₂ (_ , [] , _ , M , M' , VM , VM' , refl)
lemma51 (μ M M')  with lemma51 M
... | inj₂ (J , E , I , L , N , VL , VN , p) =
  inj₂ (J , μl E M' , I , L , N , VL , VN , cong (λ M → μ M M') p)
... | inj₁ VM with lemma51 M'
... | inj₂ (J , E , I , L , N , VL , VN , p) =
  inj₂ (J , μr VM E , I , L , N , VL , VN , cong (μ M) p)
... | inj₁ VM' = inj₁ (V-μ VM VM')
lemma51 (con c)  = inj₁ (V-con c)

variable J' : Kind

proj⇒l : {A A' B B' : ∅ ⊢⋆ *} → (A _⊢⋆_.⇒ B) ≡ (A' Type.⇒ B') → A ≡ A'
proj⇒l refl = refl

proj⇒r : {A A' B B' : ∅ ⊢⋆ *} → (A _⊢⋆_.⇒ B) ≡ (A' Type.⇒ B') → B ≡ B'
proj⇒r refl = refl

proj·l : {A : ∅ ⊢⋆ K ⇒ J}{A' : ∅ ⊢⋆ K' ⇒ J}{B : ∅ ⊢⋆ K}{B' : ∅ ⊢⋆ K'} → (A · B) ≡ (A' · B') → ∃ λ (p : K ⇒ J ≡ K' ⇒ J) → subst (∅ ⊢⋆_) p A ≡ A'
proj·l refl = refl , refl

proj·r : {A : ∅ ⊢⋆ K ⇒ J}{A' : ∅ ⊢⋆ K' ⇒ J}{B : ∅ ⊢⋆ K}{B' : ∅ ⊢⋆ K'}
  → (A · B) ≡ (A' · B') → ∃ λ (p : K' ≡ K) → subst (∅ ⊢⋆_) p B' ≡ B
proj·r refl = refl , refl

proj·l' : {A : ∅ ⊢⋆ K ⇒ J}{A' : ∅ ⊢⋆ K' ⇒ J}{B : ∅ ⊢⋆ K}{B' : ∅ ⊢⋆ K'}(p : (A · B) ≡ (A' · B')) → A ≡ subst (∅ ⊢⋆_) (sym (proj₁ (proj·l p)))  A'
proj·l' refl = refl


proj·l'' : {A : ∅ ⊢⋆ K ⇒ J}{A' : ∅ ⊢⋆ K' ⇒ J}{B : ∅ ⊢⋆ K}{B' : ∅ ⊢⋆ K'}(p : (A · B) ≡ (A' · B')) → subst (λ J₁ → ∅ ⊢⋆ J₁ ⇒ J) (proj₁ (proj·r p)) A' ≡ A
proj·l'' refl = refl

val-unique : ∀{A : ∅ ⊢⋆ K}(V V' : Value⋆ A) → V ≡ V'
val-unique (V-Π N) (V-Π .N) = refl
val-unique (V V-⇒ W) (V' V-⇒ W') =
  cong₂ _V-⇒_ (val-unique V V') (val-unique W W') 
val-unique (V-con tcn) (V-con .tcn) = refl
val-unique (V-μ V W) (V-μ V' W') =
  cong₂ V-μ (val-unique V V') (val-unique W W') 
val-unique (V-ƛ N) (V-ƛ .N) = refl


·r-cong : ∀{J J' K}(p : J ≡ J') → {A : ∅ ⊢⋆ J ⇒ K}{A' : ∅ ⊢⋆ J' ⇒ K}
  (V : Value⋆ A)(V' : Value⋆ A')(E : EvalCtx J I) → 
  (q : subst (λ J → ∅ ⊢⋆ J ⇒ K) p A ≡ A') →
  V ·r E ≡ V' ·r subst (λ J → EvalCtx J I) p E
·r-cong refl V V' E refl with val-unique V V'
... | refl = refl

subst-l⇒ : ∀ E B (p : J ≡ J') →  subst (EvalCtx *) p (E l⇒ B) ≡ subst (EvalCtx *) p E l⇒ B
subst-l⇒ E B refl = refl

subst-⇒r : ∀{A}(V : Value⋆ A) E (p : J ≡ J') →  subst (EvalCtx *) p (V ⇒r E) ≡ V ⇒r subst (EvalCtx *) p E
subst-⇒r V E refl = refl

subst-closeEvalCtx : (E : EvalCtx K J)(M : ∅ ⊢⋆ J')(p : J' ≡ J)(q : J ≡ J') →
 closeEvalCtx E (subst (_ ⊢⋆_) p M)
 ≡
 closeEvalCtx (subst (EvalCtx K) q E) M
subst-closeEvalCtx E M refl refl = refl

subst-closeEvalCtx' : (E : EvalCtx K J)(M : ∅ ⊢⋆ J)(p : K ≡ K') → 
 subst (_ ⊢⋆_) p (closeEvalCtx E M)
 ≡
 closeEvalCtx (subst (λ K → EvalCtx K J) p E) M
subst-closeEvalCtx' E M refl = refl

variable I' : Kind

subst-l· : (E : EvalCtx (J ⇒ I) K)(B : ∅ ⊢⋆ J)(p : K ≡ K')
  → subst (EvalCtx I) p (E l· B) ≡ subst (EvalCtx (J ⇒ I)) p E l· B
subst-l· E B refl = refl

subst-r· : (E : EvalCtx I K){X : ∅ ⊢⋆ I ⇒ J}(V : Value⋆ X)(p : K ≡ K')
  → subst (EvalCtx J) p (V ·r E) ≡ V ·r subst (EvalCtx I) p E
subst-r· E B refl = refl


subst-l·' : (E : EvalCtx (J ⇒ I) K)(B : ∅ ⊢⋆ J)(p : I ≡ I')
  → subst (λ I → EvalCtx I K) p (E l· B) ≡ subst (λ I → EvalCtx (J ⇒ I) K) p E l· B
subst-l·' E B refl = refl

subst-l·'' : (E : EvalCtx (J ⇒ I) K)(B : ∅ ⊢⋆ J)(B' : ∅ ⊢⋆ J')
  → (p : J ≡ J')
  → (q : J ⇒ I ≡ J' ⇒ I)
  → subst (_⊢⋆_ ∅) p B ≡ B'
  → E l· B ≡ subst (λ J → EvalCtx J K) q E l· B'
subst-l·'' E B B' refl refl refl = refl

open Relation.Binary.PropositionalEquality
cong₃ : {A : Set}{B : A → Set}{C D : Set}
      → (f : ∀ a (b : B a) → C → D) → {a a' : A}(p : a ≡ a')
      → {b : B a}{b' : B a'} → subst B p b ≡ b'
      → {c c' : C} → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

subst-Val : ∀ {A : ∅ ⊢⋆ K}{A' : ∅ ⊢⋆ K'}
  → (p : K ≡ K') → subst (∅ ⊢⋆_) p A ≡ A' → Value⋆ A' → Value⋆ A
subst-Val refl refl V = V

-- postulate mu case for now, should be similar to arrow and application
postulate
 mu-case : ∀ M (M' : ∅ ⊢⋆ K) → Value⋆ (μ M M') ⊎
  ¬ Value⋆ (μ M M') ×
  ∃
    (λ (J : Kind) →
     ∃
     (λ (E : EvalCtx * J) →
        ∃
        (λ (I : Kind) →
           ∃
           (λ (L : ∅ ⊢⋆ I ⇒ J) →
              ∃
              (λ N →
                 Value⋆ L ×
                 Value⋆ N ×
                 μ M M' ≡ closeEvalCtx E (L · N) ×
                 ((J' : Kind) (E' : EvalCtx * J') (I' : Kind) (L' : ∅ ⊢⋆ I' ⇒ J')
                  (N' : ∅ ⊢⋆ I') →
                  Value⋆ L' →
                  Value⋆ N' →
                  μ M M' ≡ closeEvalCtx E' (L' · N') →
                  ∃ (λ p → subst (EvalCtx *) p E' ≡ E)))))))
                  

lemma51! : (M : ∅ ⊢⋆ K)
  → Value⋆ M
  ⊎ ¬ (Value⋆ M)
  × ∃ λ J →
    ∃ λ (E : EvalCtx K J) →
    ∃ λ I → 
    ∃ λ (L : ∅ ⊢⋆ I ⇒ J) →
    ∃ λ (N : ∅ ⊢⋆ I) →
      Value⋆ L
    × Value⋆ N
    × M ≡ closeEvalCtx E (L · N)
    -- uniqueness condition
    × ∀ J'
      (E' : EvalCtx K J')
      I'
      (L' : ∅ ⊢⋆ I' ⇒ J')
      (N' : ∅ ⊢⋆ I') →
      Value⋆ L' →
      Value⋆ N' →
      M ≡ closeEvalCtx E' (L' · N') →
      ∃ λ (p : J' ≡ J) → subst (EvalCtx K) p E' ≡ E
lemma51! (Π M) = inj₁ (V-Π M)
lemma51! (M ⇒ M') with lemma51! M
... | inj₂ (¬VM , J , E , I , L , N , VL , VN , refl , X) =
    inj₂ ((λ { (VM V-⇒ VM') → ¬VM VM}) , J , E l⇒ M' , I , L , N , VL , VN , refl , λ { J' (VM ⇒r E') I' L' N' VL' VN' refl → ⊥-elim (¬VM VM) ; J' (E' l⇒ x) I' L' N' VL' VN' p → let (XX , YY) = X J' E' I' L' N' VL' VN' (proj⇒l p) in XX , trans (subst-l⇒ E' x (proj₁ (X J' E' I' L' N' VL' VN' (proj⇒l p)))) (cong₂ _l⇒_ YY (sym (proj⇒r p))) })
... | inj₁ VM with lemma51! M'
... | inj₂ (¬VM' , J , E , I , L , N , VL , VN , refl , X) =
  inj₂ ((λ { (VM V-⇒ VM') → ¬VM' VM'}) , J , VM ⇒r E , I , L , N , VL , VN , refl , λ { J' (V ⇒r E') I' L' N' VL' VN' p → let (XX , YY) = X J' E' I' L' N' VL' VN' (proj⇒r p) in XX , trans (subst-⇒r V E' _) (cong₃ (λ A → _⇒r_ {A = A}) (sym (proj⇒l p)) (val-unique _ _) YY) ; J' (E' l⇒ .(closeEvalCtx E (L · N))) I' L' N' VL' VN' refl → ⊥-elim (lemV· (lem0 (L' · N') E' VM))})
... | inj₁ VM' = inj₁ (VM V-⇒ VM')
lemma51! (ƛ M) = inj₁ (V-ƛ M)
lemma51! (M · M') with lemma51! M
... | inj₂ (¬VM , J , E , I , L , N , VL , VN , refl , X) =
    inj₂ ((λ()) , J , E l· M' , I , L , N , VL , VN , refl , λ{ J' [] I' L' N' VL' VN' p → ⊥-elim (¬VM (subst-Val (proj₁ (proj·l p)) (proj₂ (proj·l p)) VL'))  ; J' (x ·r E') I' L' N' VL' VN' p → ⊥-elim (¬VM (subst-Val (proj₁ (proj·l p)) (proj₂ (proj·l p)) x)) ; J' (E' l· x) I' L' N' VL' VN' p → let (XX , YY) = X J' (subst (λ K → EvalCtx K J') (sym (proj₁ (proj·l p))) E') I' L' N' VL' VN' (trans (proj·l' p) (subst-closeEvalCtx' E' (L' · N') (sym (proj₁ (proj·l p)))) ) in XX , trans (trans (cong (subst (EvalCtx _) (proj₁ (X J' (subst (λ K₃ → EvalCtx K₃ J') (sym (proj₁ (proj·l p))) E') I' L' N' VL' VN' (trans (proj·l' p) (subst-closeEvalCtx' E' (L' · N') (sym (proj₁ (proj·l p)))))))) (subst-l·'' E' x M' (proj₁ (proj·r p)) (sym (proj₁ (proj·l p))) (proj₂ (proj·r p)))) (subst-l·  (subst (λ K₂ → EvalCtx K₂ J') (sym (proj₁ (proj·l p))) E') M' (proj₁
 (X J' (subst (λ K₃ → EvalCtx K₃ J') (sym (proj₁ (proj·l p))) E') I'
  L' N' VL' VN'
  (trans (proj·l' p)
   (subst-closeEvalCtx' E' (L' · N') (sym (proj₁ (proj·l p)))))))) ) (cong (_l· M') YY) })

... | inj₁ VM with lemma51! M'
... | inj₁ VM' =
  inj₂ ((λ()) , _ , [] , _ , M , M' , VM , VM' , refl , λ{ J [] I L N VL VN p → refl , refl ; J (x ·r E) I L N VL VN p → ⊥-elim (lemV· (lem0 (L · N) E (subst-Val (proj₁ (proj·r p)) (proj₂ (proj·r p)) VM'))) ; J (E l· x) I L N VL VN p → ⊥-elim (lemV· (lem0 (L · N) E (subst-Val (proj₁ (proj·l (sym p))) (proj₂ (proj·l (sym p))) VM)))})
... | inj₂ (¬VM' , J , E , I , L , N , VL , VN , refl , X) =
  inj₂ ((λ()) , J , VM ·r E , I , L , N , VL , VN , refl , λ { J' [] I' L' N' VL' VN' p' → ⊥-elim (lemV· (lem0 (L · N) E (subst-Val (proj₁ (proj·r (sym p'))) (proj₂ (proj·r (sym p'))) VN')))  ; J' (x ·r E') I' L' N' VL' VN' p' → let (XX , YY) = X J' (subst (λ K → EvalCtx K J') (proj₁ (proj·r p')) E') I' L' N' VL' VN' (trans (sym (proj₂ (proj·r p'))) (subst-closeEvalCtx' E' (L' · N') (proj₁ (proj·r p')))) in XX , trans (trans (cong (subst (EvalCtx _) (proj₁
 (X J' (subst (λ K₃ → EvalCtx K₃ J') (proj₁ (proj·r p')) E') I' L'
  N' VL' VN'
  (trans (sym (proj₂ (proj·r p')))
   (subst-closeEvalCtx' E' (L' · N') (proj₁ (proj·r p'))))))) (·r-cong (proj₁ (proj·r p')) x VM E' (proj·l'' p'))) (subst-r· (subst (λ K₂ → EvalCtx K₂ J') (proj₁ (proj·r p')) E') VM XX)) (cong (VM ·r_) YY) ; J' (E' l· x) I' L' N' VL' VN' p' → ⊥-elim (lemV· (lem0 (L' · N') E' (subst-Val (proj₁ (proj·l (sym p'))) (proj₂ (proj·l (sym p'))) VM)))})
lemma51! (μ M M') = mu-case M M'
lemma51! (con x) = inj₁ (V-con x)

-- this one is specialised to having types of the same kind
postulate
  uniqueness : (A : ∅ ⊢⋆ K)
           → ¬ (Value⋆ A)
           → (B : ∅ ⊢⋆ J)
           → (E : EvalCtx K J)(E' : EvalCtx K J)
           → A ≡ closeEvalCtx E B
           → A ≡ closeEvalCtx E' B
           → E ≡ E'
-- the above lemma51! isn't directly useful as it wants a (L · N) not a B...

{-
det : (p : A —→E B)(q : A —→E B') → B ≡ B'
-}
```

```
v-refl :  (A B : ∅ ⊢⋆ K)(V : Value⋆ A) → A —↠E B → A ≡ B
v-refl A .A V refl—↠E       = refl
v-refl A B V (trans—↠E p q) = ⊥-elim (notboth A (V , _ , p)) 
```
