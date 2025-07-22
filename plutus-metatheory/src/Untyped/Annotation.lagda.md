---
title: Untyped.Annotations
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
open import Data.List.Relation.Unary.All using (All;fromList)
open import Builtin using (Builtin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_;proj₁;_,_)
```
The content of the annotation can be from any arbitrary set
(although it has to be the same set all the way down the tree).

The `Annotation` type deliberatly parallels the term type (`_⊢`) so
that all the information from the underlying term exists and the
annotations can be `strip`ed.
```
variable
  X X' : Set
  L M N : X ⊢
  Ms : List (X ⊢)

data Annotation (A : Set) : X ⊢ → Set₁ where
  ⟨_⟩[`_] : (a : A) → (v : X) → Annotation A (` v)
  ⟨_⟩[ƛ_] : (a : A) → Annotation A N → Annotation A (ƛ N)
  ⟨_⟩[_·_] : (a : A) → Annotation A L → Annotation A M → Annotation A (L · M)
  ⟨_⟩[force_] : (a : A) → Annotation A N → Annotation A (force N)
  ⟨_⟩[delay_] : (a : A) → Annotation A N → Annotation A (delay N)
  ⟨_⟩[con_] : (a : A) → (t : TmCon) → Annotation A {X} (con t)
  ⟨_⟩[error] : (a : A) → Annotation A {X} error
  ⟨_⟩[builtin_] : (a : A) → (b : Builtin) → Annotation A {X} (builtin b)
  ⟨_⟩[case_-_] : (a : A) → (t : Annotation A L) → (ts : All (Annotation A) Ms) → Annotation A (case L Ms)
  ⟨_⟩[constr_-_] : (a : A) → (i : ℕ) → (ts : All (Annotation A) Ms) → Annotation A (constr i Ms)

Annotation′ : Set → X ⊢ → Set₁

data Annotation″ (A : Set) : X ⊢ → Set₁ where
  ` : (v : X) → Annotation″ A (` v)
  ƛ : (NN : Annotation′ A N) → Annotation″ A (ƛ N)
  _·_ : (LL : Annotation′ A L) → (MM : Annotation′ A M) → Annotation″ A (L · M)
  force : (MM : Annotation′ A M) → Annotation″ A (force M)
  delay : (MM : Annotation′ A M) → Annotation″ A (delay M)
  con : (t : TmCon) → Annotation″ A {X} (con t)
  error : Annotation″ A {X} error
  builtin : (b : Builtin) → Annotation″ A {X} (builtin b)
  case : (t : Annotation′ A L) → (ts : All (Annotation′ A) Ms) → Annotation″ A (case L Ms)
  constr : (i : ℕ) → (ts : All (Annotation′ A) Ms) → Annotation″ A (constr i Ms)

Annotation′ A N = A × (Annotation″ A N)

read : {A : Set} → Annotation′ A M → A
read = proj₁

{-# TERMINATING #-}
strip : {A : Set} {M : X ⊢} → Annotation′ A M → X ⊢
strip {M = M} _ = M

unannotated : {A : Set} → (default : A) → (M : X ⊢) → Annotation′ A M
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

```
