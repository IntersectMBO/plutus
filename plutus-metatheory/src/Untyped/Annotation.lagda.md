---
title: Untyped.Annotation
layout: page
---

# Annotations over Untyped terms
```
module Untyped.Annotation where

```
## Imports

```
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Data.Maybe using (Maybe; just; nothing)
open import RawU using (TmCon)
open import Data.List using (List; map)
open import Data.List.Relation.Unary.All using (All)
open import Builtin using (Builtin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_;proj₁;_,_)
open import Untyped.RenamingSubstitution using (weaken; Ren; lift; ren; renList)
open import Relation.Binary.Core using (REL)
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
```
The content of the annotation can be from any arbitrary set
(although it has to be the same set all the way down the tree).

The `Annotation` type deliberatly parallels the term type (`_⊢`) so
that all the information from the underlying term exists and the
annotations can be `strip`ed.
```
variable
  X X' A B Y : Set
  L M N : X ⊢
  Ms : List (X ⊢)

Annotation : Set → X ⊢ → Set₁

data Annotation′ (A : Set) : X ⊢ → Set₁ where
  ` : (v : X) → Annotation′ A (` v)
  ƛ : (NN : Annotation A N) → Annotation′ A (ƛ N)
  _·_ : (LL : Annotation A L) → (MM : Annotation A M) → Annotation′ A (L · M)
  force : (MM : Annotation A M) → Annotation′ A (force M)
  delay : (MM : Annotation A M) → Annotation′ A (delay M)
  con : (t : TmCon) → Annotation′ A {X} (con t)
  error : Annotation′ A {X} error
  builtin : (b : Builtin) → Annotation′ A {X} (builtin b)
  case : (t : Annotation A L) → (ts : All (Annotation A) Ms) → Annotation′ A (case L Ms)
  constr : (i : ℕ) → (ts : All (Annotation A) Ms) → Annotation′ A (constr i Ms)

Annotation A N = A × (Annotation′ A N)

read : Annotation A M → A
read = proj₁

{-# TERMINATING #-}
strip : {M : X ⊢} → Annotation A M → X ⊢
strip {M = M} _ = M

```
In the same way that we can weaken terms, we need to be able to weaken
annotated terms. This requires a general notion of renaming over annotations
so that we can recurse through lambdas.
```

renAnn′ : (ρ : Ren X X') → Annotation′ A M → Annotation′ A (ren ρ M)
renAnn : (ρ : Ren X X') → Annotation A M → Annotation A (ren ρ M)
listRenAnn : (ρ : Ren X X') → All (Annotation A) Ms → All (Annotation A) (renList ρ Ms)

renAnn ρ (a , t) = a , renAnn′ ρ t
listRenAnn ρ All.[] = All.[]
listRenAnn ρ (a All.∷ as) = renAnn ρ a All.∷ (listRenAnn ρ as)

renAnn′ ρ (` v) = ` (ρ v)
renAnn′ ρ (ƛ NN) = ƛ (renAnn (lift ρ) NN)
renAnn′ ρ (LL · MM) = (renAnn ρ LL) · (renAnn ρ MM)
renAnn′ ρ (force MM) = force (renAnn ρ MM)
renAnn′ ρ (delay MM) = delay (renAnn ρ MM)
renAnn′ ρ (con t) = con t
renAnn′ ρ error = error
renAnn′ ρ (builtin b) = builtin b
renAnn′ ρ (case t ts) = case (renAnn ρ t) (listRenAnn ρ ts)
renAnn′ ρ (constr i ts) = constr i (listRenAnn ρ ts)

weakenAnnotation : {M : X ⊢} → Annotation A M → Annotation A (weaken M)
weakenAnnotation a = renAnn just a
```
It is sometimes useful to convert a term into an Annotated term,
but with some default (usually blank) annotation.
```

unannotatedAll : {A : Set} → (default : A) → (Ms : List (X ⊢)) → All (Annotation A) Ms
unannotated : {A : Set} → (default : A) → (M : X ⊢) → Annotation A M

unannotatedAll d List.[] = All.[]
unannotatedAll d (m List.∷ ms) = unannotated d m All.∷ unannotatedAll d ms

unannotated d (` x) = d , ` x
unannotated d (ƛ N) = d , ƛ (unannotated d N)
unannotated d (L · M) = d , (unannotated d L · unannotated d M)
unannotated d (force M) = d , force (unannotated d M)
unannotated d (delay M) = d , delay (unannotated d M)
unannotated d (con x) = d , con x
unannotated d (constr i xs) = d , constr i (unannotatedAll d xs)
unannotated d (case L ts) = d , case (unannotated d L) (unannotatedAll d ts)
unannotated d (builtin b) = d , builtin b
unannotated d error = d , error

```
Pointwise comparisons are useful over lists. We need to be able to apply things
over lists that are `All` annotated
```
variable
  a b 𝓁 : Level

data PointwiseAll {A : X → Set a} {B : Y → Set b} (R : {x : X} {y : Y} → A x → B y → Set 𝓁)
               : {Xs : List X} {Ys : List Y} → All A Xs → All B Ys → Set (a ⊔ b ⊔ 𝓁) where
               [] : PointwiseAll R All.[] All.[]
               _∷_ : {x : X} {y : Y} {xs : List X} {ys : List Y}
                     → {ax : A x} {by : B y}
                     → {axs : All A xs} {bys : All B ys}
                     → R ax by → PointwiseAll R axs bys → PointwiseAll R (ax All.∷ axs) (by All.∷ bys)

data PointwiseAllᵣ {X : Set a} {B : Y → Set b} (R : X → {y : Y} → B y → Set (a ⊔ b))
               : {Ys : List Y} → List X → All B Ys → Set (a ⊔ b) where
               [] : PointwiseAllᵣ R List.[] All.[]
               _∷_ : {x : X} {xs : List X} {y : Y} {ys : List Y}
                     → {by : B y}
                     → {bys : All B ys}
                     → R x by → PointwiseAllᵣ R xs bys → PointwiseAllᵣ R (x List.∷ xs) (by All.∷ bys)

data PointwiseAllₗ {A : X → Set a} (R : {x : X} → A x → Y → Set b)
               : {Xs : List X} → All A Xs → List Y → Set (a ⊔ b) where
               [] : PointwiseAllₗ R All.[] List.[]
               _∷_ : {x : X} {xs : List X} {y : Y} {ys : List Y}
                     → {ax : A x}
                     → {axs : All A xs}
                     → R ax y → PointwiseAllₗ R axs ys → PointwiseAllₗ R (ax All.∷ axs) (y List.∷ ys)

```
# Deciding Pointwise All
```
open import VerifiedCompilation.Certificate using (ProofOrCE; proof; ce; MatchOrCE; matchOrCE; SimplifierTag)

pcePointwiseAllᵣ : {X : Set a} {B : Y → Set b} {R : X → {y : Y} → B y → Set (a ⊔ b)}
                 → SimplifierTag
                 → ((x : X) → {y : Y} → (by : B y) → ProofOrCE {𝓂 = a} {𝓃 = b} (R x by))
                 → {Ys : List Y}
                 → (xs : List X)
                 → (bys : All B Ys)
                 → ProofOrCE {𝓂 = a} {𝓃 = b} (PointwiseAllᵣ R xs bys)
pcePointwiseAllᵣ tag isR? List.[] All.[] = ProofOrCE.proof []
pcePointwiseAllᵣ {X = X} tag isR? List.[] (px All.∷ ys) = ce {X = List X} (λ ()) tag List.[] (px All.∷ ys)
pcePointwiseAllᵣ {B = B} {R = R} tag isR? {Ys = Ys} (x List.∷ xs) All.[] = ce {X' = All B Ys} (λ ()) tag (x List.∷ xs) All.[]
pcePointwiseAllᵣ tag isR? (x List.∷ xs) (px All.∷ ys) with isR? x px
... | ce ¬p t b a = ce (λ { (x ∷ xx) → ¬p x} ) t b a
... | proof p with pcePointwiseAllᵣ tag isR? xs ys
...    | ce ¬p t b a = ce (λ { (x ∷ xx) → ¬p xx} ) t b a
...    | proof ps = proof (p ∷ ps)
```
# Examples

```

open import Data.Empty using (⊥)

postulate
  x y : X

t₁ : X ⊢
t₁ = ((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` x)) · (` y)

t₁' : X ⊢
t₁' = ((` x) · (` y))


A₁ : Annotation {X = X} ℕ t₁
A₁ = (0 , ((0 , ((0 , ƛ
                      (0 ,
                       ƛ (0 , ((0 , ` (just nothing)) · (0 , ` nothing))))) · (0 , ` x))) · (0 , ` y)))

A₁' : Annotation {X = X} ℕ t₁'
A₁' = (2 , ((0 , (` x)) · (0 , (` y))))

```
We need to show `A₁ ==> A₁'`

[] <> 0
(0 , ((0 , ((0 , ƛ (0 , ƛ (0 , ((0 , ` (just nothing)) · (0 , ` nothing))))) · (0 , ` a))) · (0 , ` b)))
(2 , ((0 , (` a)) · (0 , (` b))))

= c· =>

[` b] <> 1
(0 , ((0 , ƛ (0 , ƛ (0 , ((0 , ` (just nothing)) · (0 , ` nothing))))) · (0 , ` a)))
(1 , ((0 , (` a)) · (0 , (` b))))

= c· =>

[` a , ` b] <> 2
(0 , ƛ (0 , ƛ (0 , ((0 , ` (just nothing)) · (0 , ` nothing)))))
(0 , ((0 , (` a)) · (0 , (` b))))

= cƛ =>

[` b] <(0 , ` a)> 1
(0 , ƛ (0 , ((0 , ` (just nothing)) · (0 , ` nothing))))
(0 , ((0 , (` a)) · (0 , (` b))))

= cƛ =>

[] <(1 , ` a) , (0 , ` b)> 0
(0 , ((0 , ` (just nothing)) · (0 , ` nothing)))
(0 , ((0 , (` a)) · (0 , (` b))))

= _·_ =>

  [] <(1 , ` a) , (0 , ` b)> 0
  (0 , ` (just nothing))
  (0 , (` a))

  = sub =>

  [] <(1 , ` a) , (0 , ` b)> 0
  (0 , (` a))
  (0 , (` a))

  = refl =>

  QED

&&

  [] <(1 , ` a) , (0 , ` b)> 0
  (0 , ` nothing)
  (0 , (` b))

  = sub =>

  [] <(1 , ` a) , (0 , ` b)> 0
  (0 , (` b))
  (0 , (` b))

  = refl =>

  QED
