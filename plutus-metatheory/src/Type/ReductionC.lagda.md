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

open import Relation.Binary.PropositionalEquality
  using (_≡_;refl;cong;subst;trans;sym;inspect) renaming ([_] to blah)
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
infix 2 _—↠⋆_

data _—→⋆_ : ∀{J} → (∅ ⊢⋆ J) → (∅ ⊢⋆ J) → Set where
  contextRule : ∀{K K'} → (E : EvalCtx K K')
    → ∀{A A' : ∅ ⊢⋆ K'}
    → A —→⋆ A'
    → {B B' : ∅ ⊢⋆ K}
    → B  ≡ closeEvalCtx E A
    → B' ≡ closeEvalCtx E A'
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
... | step p = step (contextRule (μl [] B) p refl refl)
... | done VA with progress⋆ B
... | step p = step (contextRule (μr VA []) p refl refl)
... | done VB = done (V-μ VA VB)
progress⋆ (Π A) = done (V-Π A)
progress⋆ (A ⇒ B) with progress⋆ A
... | step p = step (contextRule ([] l⇒ B) p refl refl)
... | done VA with progress⋆ B
... | step q = step (contextRule (VA ⇒r []) q refl refl)
... | done VB = done (VA V-⇒ VB)
progress⋆ (ƛ A) = done (V-ƛ A)
progress⋆ (A · B) with progress⋆ A
... | step p =
  step (contextRule ([] l· B) p refl refl)
... | done V with progress⋆ B
... | step p =
  step (contextRule (V ·r []) p refl refl)
progress⋆ (.(ƛ _) · B) | done (V-ƛ A) | done VB = step (β-ƛ VB)
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

notboth : (A : ∅ ⊢⋆ K) → ¬ (Value⋆ A × (Σ (∅ ⊢⋆ K) (A —→⋆_)))
notboth A (V , A' , contextRule [] p refl refl) = notboth A (V , A' , p)
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

-- this is rather unpleasant with this definition of closeEvalCtx
-- it's do-able but ugly, some lemmas would be useful rather than using 'with'
{-
det : (p : A —→⋆ B)(q : A —→⋆ B') → B ≡ B'
det (contextRule [] p refl refl) C@(contextRule _ _ _ _) = det p C
det C@(contextRule (_ ·r _) _ _ _) (contextRule [] q refl refl) = det C q
det (contextRule (V ·r E) {A = B}{A' = B'} p x x') (contextRule (V' ·r E') {A = C}{A' = C'} q x'' x''')
  with closeEvalCtx E B
  | inspect (closeEvalCtx E) B
  | closeEvalCtx E B'
  | inspect (closeEvalCtx E) B'
  | closeEvalCtx E' C
  | inspect (closeEvalCtx E') C
  | closeEvalCtx E' C'
  | inspect (closeEvalCtx E') C'
det (contextRule (V ·r E) p refl refl) (contextRule (V' ·r E') q refl refl)
  | r
  | blah x
  | r'
  | blah x'
  | .r
  | blah x''
  | r'''
  | blah x''' = cong
    (_ ·_)
    (det (contextRule E p (sym x) (sym x'))
         (contextRule E' q (sym x'') (sym x''')))
det (contextRule (x₄ ·r E) p x x₁) (contextRule (E₁ l· x₅) q x₂ x₃) = {!!}
det (contextRule (x₄ ·r E) p x x₁) (contextRule (x₅ ⇒r E₁) q x₂ x₃) = {!!}
det (contextRule (x₄ ·r E) p x x₁) (contextRule (E₁ l⇒ x₅) q x₂ x₃) = {!!}
det (contextRule (x₄ ·r E) p x x₁) (contextRule (μr x₅ E₁) q x₂ x₃) = {!!}
det (contextRule (x₄ ·r E) p x x₁) (contextRule (μl E₁ B) q x₂ x₃) = {!!}
det (contextRule (E l· x₄) p x x₁) (contextRule [] q x₂ x₃) = {!!}
det (contextRule (E l· x₄) p x x₁) (contextRule (x₅ ·r E₁) q x₂ x₃) = {!!}
det (contextRule (E l· x₄) p x x₁) (contextRule (E₁ l· x₅) q x₂ x₃) = {!!}
det (contextRule (E l· x₄) p x x₁) (contextRule (x₅ ⇒r E₁) q x₂ x₃) = {!!}
det (contextRule (E l· x₄) p x x₁) (contextRule (E₁ l⇒ x₅) q x₂ x₃) = {!!}
det (contextRule (E l· x₄) p x x₁) (contextRule (μr x₅ E₁) q x₂ x₃) = {!!}
det (contextRule (E l· x₄) p x x₁) (contextRule (μl E₁ B) q x₂ x₃) = {!!}
det (contextRule (x₄ ⇒r E) p x x₁) (contextRule [] q x₂ x₃) = {!!}
det (contextRule (x₄ ⇒r E) p x x₁) (contextRule (x₅ ·r E₁) q x₂ x₃) = {!!}
det (contextRule (x₄ ⇒r E) p x x₁) (contextRule (E₁ l· x₅) q x₂ x₃) = {!!}
det (contextRule (x₄ ⇒r E) p x x₁) (contextRule (x₅ ⇒r E₁) q x₂ x₃) = {!!}
det (contextRule (x₄ ⇒r E) p x x₁) (contextRule (E₁ l⇒ x₅) q x₂ x₃) = {!!}
det (contextRule (x₄ ⇒r E) p x x₁) (contextRule (μr x₅ E₁) q x₂ x₃) = {!!}
det (contextRule (x₄ ⇒r E) p x x₁) (contextRule (μl E₁ B) q x₂ x₃) = {!!}
det (contextRule (E l⇒ x₄) p x x₁) (contextRule [] q x₂ x₃) = {!!}
det (contextRule (E l⇒ x₄) p x x₁) (contextRule (x₅ ·r E₁) q x₂ x₃) = {!!}
det (contextRule (E l⇒ x₄) p x x₁) (contextRule (E₁ l· x₅) q x₂ x₃) = {!!}
det (contextRule (E l⇒ x₄) p x x₁) (contextRule (x₅ ⇒r E₁) q x₂ x₃) = {!!}
det (contextRule (E l⇒ x₄) p x x₁) (contextRule (E₁ l⇒ x₅) q x₂ x₃) = {!!}
det (contextRule (E l⇒ x₄) p x x₁) (contextRule (μr x₅ E₁) q x₂ x₃) = {!!}
det (contextRule (E l⇒ x₄) p x x₁) (contextRule (μl E₁ B) q x₂ x₃) = {!!}
det (contextRule (μr x₄ E) p x x₁) (contextRule [] q x₂ x₃) = {!!}
det (contextRule (μr x₄ E) p x x₁) (contextRule (x₅ ·r E₁) q x₂ x₃) = {!!}
det (contextRule (μr x₄ E) p x x₁) (contextRule (E₁ l· x₅) q x₂ x₃) = {!!}
det (contextRule (μr x₄ E) p x x₁) (contextRule (x₅ ⇒r E₁) q x₂ x₃) = {!!}
det (contextRule (μr x₄ E) p x x₁) (contextRule (E₁ l⇒ x₅) q x₂ x₃) = {!!}
det (contextRule (μr x₄ E) p x x₁) (contextRule (μr x₅ E₁) q x₂ x₃) = {!!}
det (contextRule (μr x₄ E) p x x₁) (contextRule (μl E₁ B) q x₂ x₃) = {!!}
det (contextRule (μl E B) p x x₁) (contextRule [] q x₂ x₃) = {!!}
det (contextRule (μl E B) p x x₁) (contextRule (x₄ ·r E₁) q x₂ x₃) = {!!}
det (contextRule (μl E B) p x x₁) (contextRule (E₁ l· x₄) q x₂ x₃) = {!!}
det (contextRule (μl E B) p x x₁) (contextRule (x₄ ⇒r E₁) q x₂ x₃) = {!!}
det (contextRule (μl E B) p x x₁) (contextRule (E₁ l⇒ x₄) q x₂ x₃) = {!!}
det (contextRule (μl E B) p x x₁) (contextRule (μr x₄ E₁) q x₂ x₃) = {!!}
det (contextRule (μl E B) p x x₁) (contextRule (μl E₁ B₁) q x₂ x₃) = {!!}
det (contextRule E p x x₁) (β-ƛ x₂) = {!!}
det (β-ƛ x) (contextRule E q x₁ x₂) = {!!}
det (β-ƛ x) (β-ƛ x₁) = {!!}
-}
```
