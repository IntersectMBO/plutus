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
open import Untyped.RenamingSubstitution using (weaken)
```
The content of the annotation can be from any arbitrary set
(although it has to be the same set all the way down the tree).

The `Annotation` type deliberatly parallels the term type (`_⊢`) so
that all the information from the underlying term exists and the
annotations can be `strip`ed.
```
variable
  X X' A : Set
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

postulate
  weakenAnnotation' : {M : X ⊢} → Annotation′ A M → Annotation′ A (weaken M)

weakenAnnotation : {M : X ⊢} → Annotation A M → Annotation A (weaken M)
{-
weakenAnnotation' (` v) = ` (just v)
weakenAnnotation' (ƛ NN) = ƛ (weakenAnnotation NN)
weakenAnnotation' (LL · MM) = {!!}
weakenAnnotation' (force MM) = {!!}
weakenAnnotation' (delay MM) = {!!}
weakenAnnotation' (con t) = con t
weakenAnnotation' error = error
weakenAnnotation' (builtin b) = builtin b
weakenAnnotation' (case t ts) = {!!}
weakenAnnotation' (constr i ts) = {!!}
-}

weakenAnnotation (a , a') = (a , (weakenAnnotation' a'))

{-
unannotated : {A : Set} → (default : A) → (M : X ⊢) → Annotation A M
unannotated d (` x) = d , ` x
unannotated d (ƛ N) = d , ƛ (unannotated d N)
unannotated d (L · M) = d , (unannotated d L · unannotated d M)
unannotated d (force M) = d , force (unannotated d M)
unannotated d (delay M) = d , delay (unannotated d M)
unannotated d (con x) = d , con x
unannotated d (constr i xs) = d , constr i {!!}
unannotated d (case L ts) = d , {!!}
unannotated d (builtin b) = d , builtin b
unannotated d error = d , error
-}

```
# Examples

```

open import Data.Empty using (⊥)

postulate
  a b : X

t₁ : X ⊢
t₁ = ((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b)

t₁' : X ⊢
t₁' = ((` a) · (` b))


A₁ : Annotation {X = X} ℕ t₁
A₁ = (0 , ((0 , ((0 , ƛ
                      (0 ,
                       ƛ (0 , ((0 , ` (just nothing)) · (0 , ` nothing))))) · (0 , ` a))) · (0 , ` b)))

A₁' : Annotation {X = X} ℕ t₁'
A₁' = (2 , ((0 , (` a)) · (0 , (` b))))

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
