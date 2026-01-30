---
title: VerifiedCompilation.UntypedViews
layout: page
---
# Predicates and View Types for Untyped Terms
```
module VerifiedCompilation.UntypedViews where

open import Untyped using (_⊢; `; ƛ; case; constr; _·_; force; delay; con; builtin; error)
open import Relation.Unary as Unary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Utils as U using (Maybe; nothing; just; Either)
open import Relation.Nullary using (_×-dec_)
open import Data.Product using (_,_)
open import RawU using (TmCon)
open import Builtin using (Builtin)
open import Untyped.Equality using (decEq-⊢)
open import Data.List using (List; [_])
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; zero)
open import Function using (_∋_)

```
## Pattern Views for Terms

Because many of the translations only run on a very specific AST pattern, we need a
[View](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/view-from-the-left/F8A44CAC27CCA178AF69DD84BC585A2D)
to recognise that pattern and extract the variables.

Following suggestions from Philip Wadler: creating Views for each Term type and then
allowing them to accept arbitrary sub-views should make this reusable. We can create
patterns using nested calls to these views, and decide them with nested calls to the
decision procedures.
```

Pred : Set₁
Pred = {X : ℕ} → (X ⊢) → Set

ListPred : Set₁
ListPred = {X : ℕ} → List (X ⊢) → Set

data isVar { X : ℕ } : (X ⊢) → Set where
  isvar : (v : Fin X) → isVar (` v)
isVar? : {X : ℕ} → Decidable (isVar {X})
isVar? (` x) = yes (isvar x)
isVar? (ƛ x) = no λ ()
isVar? (x · x₁) = no (λ ())
isVar? (force x) = no (λ ())
isVar? (delay x) = no (λ ())
isVar? (con x) = no (λ ())
isVar? (constr i xs) = no (λ ())
isVar? (case x ts) = no (λ ())
isVar? (builtin b) = no (λ ())
isVar? error = no (λ ())

data isLambda (P : Pred) { X : ℕ } : (X ⊢) → Set where
  islambda : {t : (suc X ⊢)} → P t → isLambda P (ƛ t)
isLambda? : {X : ℕ} {P : Pred} → ({X : ℕ} → Decidable (P {X})) → Decidable (isLambda P {X})
isLambda? isP? (` x) = no λ ()
isLambda? isP? (ƛ t) with isP? t
...                                | no ¬p = no λ { (islambda x) → ¬p x}
...                                | yes p = yes (islambda p)
isLambda? isP? (t _⊢.· t₁) = no (λ ())
isLambda? isP? (_⊢.force t) = no (λ ())
isLambda? isP? (_⊢.delay t) = no (λ ())
isLambda? isP? (_⊢.con x) = no (λ ())
isLambda? isP? (constr i xs) = no (λ ())
isLambda? isP? (case t ts) = no (λ ())
isLambda? isP? (_⊢.builtin b) = no (λ ())
isLambda? isP? _⊢.error = no (λ ())

data isApp (P Q : Pred) {X : ℕ}  : (X ⊢) → Set where
  isapp : {l r : (X ⊢)} → P l → Q r → isApp P Q (l · r)
isApp? : {X : ℕ} → {P Q : Pred} → ({X : ℕ} → Decidable (P {X})) → ({X : ℕ} → Decidable (Q {X})) → Decidable (isApp P Q {X})
isApp? isP? isQ? (` x) = no (λ ())
isApp? isP? isQ? (ƛ t) = no (λ ())
isApp? isP? isQ? (t · t₁) with (isP? t) ×-dec (isQ? t₁)
...                                    | no ¬p = no λ { (isapp x x₁) → ¬p (x , x₁)}
...                                    | yes (p , q) = yes (isapp p q)
isApp? isP? isQ? (force t) = no (λ ())
isApp? isP? isQ? (delay t) = no (λ ())
isApp? isP? isQ? (con x) = no (λ ())
isApp? isP? isQ? (constr i xs) = no (λ ())
isApp? isP? isQ? (case t ts) = no (λ ())
isApp? isP? isQ? (builtin b) = no (λ ())
isApp? isP? isQ? error = no (λ ())

data isForce (P : Pred) {X : ℕ} : (X ⊢) → Set where
  isforce : {t : (X ⊢)} → P t → isForce P (force t)
isForce? : {X : ℕ} → {P : Pred} → ({X : ℕ} → Decidable (P {X})) → Decidable (isForce P {X})
isForce? isP? (` x) = no (λ ())
isForce? isP? (ƛ t) = no (λ ())
isForce? isP? (t · t₁) = no (λ ())
isForce? isP? (force t) with isP? t
...                                  | no ¬p = no λ { (isforce x) → ¬p x}
...                                  | yes p = yes (isforce p)
isForce? isP? (delay t) = no (λ ())
isForce? isP? (con x) = no (λ ())
isForce? isP? (constr i xs) = no (λ ())
isForce? isP? (case t ts) = no (λ ())
isForce? isP? (builtin b) = no (λ ())
isForce? isP? error = no (λ ())


data isDelay (P : Pred) {X : ℕ} : (X ⊢) → Set where
  isdelay : {t : (X ⊢)} → P t → isDelay P (delay t)
isDelay? : {X : ℕ} → {P : Pred} → ({X : ℕ} → Decidable (P {X})) → Decidable (isDelay P {X})
isDelay? isP? (` x) = no (λ ())
isDelay? isP? (ƛ t) = no (λ ())
isDelay? isP? (t · t₁) = no (λ ())
isDelay? isP? (force t) = no (λ ())
isDelay? isP? (delay t) with isP? t
...                                  | yes p = yes (isdelay p)
...                                  | no ¬p = no λ { (isdelay x) → ¬p x }
isDelay? isP? (con x) = no (λ ())
isDelay? isP? (constr i xs) = no (λ ())
isDelay? isP? (case t ts) = no (λ ())
isDelay? isP? (builtin b) = no (λ ())
isDelay? isP? error = no (λ ())

data isCon {X : ℕ} : (X ⊢) → Set where
  iscon : (t : TmCon)  → isCon {X} (con t)
isCon? : {X : ℕ} → Decidable (isCon {X})
isCon? (` x) = no (λ ())
isCon? (ƛ t) = no (λ ())
isCon? (t · t₁) = no (λ ())
isCon? (force t) = no (λ ())
isCon? (delay t) = no (λ ())
isCon? (con c) = yes (iscon c)
isCon? (constr i xs) = no (λ ())
isCon? (case t ts) = no (λ ())
isCon? (builtin b) = no (λ ())
isCon? error = no (λ ())

data isConstr (Qs : ListPred) {X : ℕ} : (X ⊢) → Set where
  isconstr : (i : ℕ) → {xs : List (X ⊢)} → Qs xs → isConstr Qs (constr i xs)
isConstr? : {X : ℕ} → {Qs : ListPred} → ({X : ℕ} → Decidable (Qs {X})) → Decidable (isConstr Qs {X})
isConstr? isQs? (` x) = no (λ())
isConstr? isQs? (ƛ t) = no (λ())
isConstr? isQs? (t · t₁) = no (λ())
isConstr? isQs? (force t) = no (λ())
isConstr? isQs? (delay t) = no (λ())
isConstr? isQs? (con x) = no (λ())
isConstr? isQs? (constr i xs) with isQs? xs
...                                           | no ¬q = no λ { (isconstr i₁ q) → ¬q q }
...                                           | yes q = yes (isconstr i q)
isConstr? isQs? (case t ts) = no (λ())
isConstr? isQs? (builtin b) = no (λ())
isConstr? isQs? error = no (λ())

data isCase (P : Pred) (Qs : ListPred) { X : ℕ } : (X ⊢) → Set where
  iscase : {t : (X ⊢)} → {ts : List (X ⊢)} → P t → Qs ts → isCase P Qs (case t ts)
isCase? : {X : ℕ} → {P : Pred} → {Qs : ListPred} → ({X : ℕ} → Decidable (P {X})) → ({X : ℕ} → Decidable (Qs {X})) → Decidable (isCase P Qs {X})
isCase? isP? isQs? (` x) = no (λ ())
isCase? isP? isQs? (ƛ t) = no (λ ())
isCase? isP? isQs? (t · t₁) = no (λ ())
isCase? isP? isQs? (force t) = no (λ ())
isCase? isP? isQs? (delay t) = no (λ ())
isCase? isP? isQs? (con x) = no (λ ())
isCase? isP? isQs? (constr i xs) = no (λ ())
isCase? isP? isQs? (case t ts) with (isP? t) ×-dec (isQs? ts)
...                                            | no ¬pqs = no λ { (iscase p qs) → ¬pqs (p , qs)}
...                                            | yes (p , qs) = yes (iscase p qs)
isCase? isP? isQs? (builtin b) = no (λ ())
isCase? isP? isQs? error = no (λ ())

data isBuiltin {X : ℕ} : (X ⊢) → Set where
  isbuiltin : (b : Builtin) → isBuiltin {X} (builtin b)
isBuiltin? : {X : ℕ} → Decidable (isBuiltin {X})
isBuiltin? (` x) = no (λ ())
isBuiltin? (ƛ t) = no (λ ())
isBuiltin? (t · t₁) = no (λ ())
isBuiltin? (force t) = no (λ ())
isBuiltin? (delay t) = no (λ ())
isBuiltin? (con x) = no (λ ())
isBuiltin? (constr i xs) = no (λ ())
isBuiltin? (case t ts) = no (λ ())
isBuiltin? (builtin b) = yes (isbuiltin b)
isBuiltin? error = no (λ ())

data isError {X : ℕ} : (X ⊢) → Set where
  iserror : isError {X} error
isError? : {X : ℕ} → Decidable (isError {X})
isError? (` x) = no (λ ())
isError? (ƛ t) = no (λ ())
isError? (t · t₁) = no (λ ())
isError? (force t) = no (λ ())
isError? (delay t) = no (λ ())
isError? (con x) = no (λ ())
isError? (constr i xs) = no (λ ())
isError? (case t ts) = no (λ ())
isError? (builtin b) = no (λ ())
isError? error = yes iserror
```
Some basic views that will match any Term, to be used for "wildcard" parts of the pattern.
```
data isTerm { X : ℕ } : (X ⊢) → Set where
  isterm : (t : X ⊢) → isTerm t
isTerm? : {X : ℕ} → Decidable (isTerm {X})
isTerm? t = yes (isterm t)

data allTerms { X : ℕ } : List (X ⊢) → Set where
  allterms : (ts : List (X ⊢)) → allTerms ts
allTerms? : {X : ℕ} → Decidable (allTerms {X})
allTerms? ts = yes (allterms ts)
```
## An Example
```
data TestPat {X : ℕ} : (X ⊢) → Set where
  tp : (t : X ⊢) (ts ts₂ : List (X ⊢)) → TestPat {X} (case (case t ts) ts₂)
isTestPat? : {X : ℕ} → Decidable (TestPat {X})
isTestPat? v with isCase? (isCase? isTerm? allTerms?) allTerms? v
... | yes (iscase (iscase (isterm t) (allterms ts)) (allterms ts₁)) = yes (tp t ts ts₁)
... | no ¬tp = no λ { (tp t ts ts₂) → ¬tp (iscase (iscase (isterm t) (allterms ts)) (allterms ts₂)) }

```
