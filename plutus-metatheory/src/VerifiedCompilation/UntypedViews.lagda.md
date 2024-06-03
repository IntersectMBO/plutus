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
open import Relation.Nullary.Product using (_×-dec_)
open import Data.Product using (_,_)
open import RawU using (TmCon)
open import Builtin using (Builtin)
```
## Pattern Views for Terms

Because many of the translations only run on a very specific AST pattern, we need a
[View](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/view-from-the-left/F8A44CAC27CCA178AF69DD84BC585A2D)
to recognise that pattern and extract the variables.

Following suggestions from Philip Wadler: creating Views for each Term type and then allowing them to accept arbitrary sub-views should
make this reusable. We can create patterns using nested calls to these views, and decide them with nested calls to the decision procedures. 
```

Pred : Set₁
Pred = ∀{X} → (X ⊢) → Set

data isVar (X : Set) : Pred where
  isvar : (v : X) → isVar X (` v)
isVar? : {X : Set} → Decidable (isVar X)
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

data isLambda (X : Set) (P : Pred) : Pred where
  islambda : (t : ((Maybe X) ⊢)) → P t → isLambda X P (ƛ t)
isLambda? : {X : Set} → {P : Pred} → (Decidable P) → Decidable (isLambda X P)
isLambda? isP? (` x) = no λ ()
isLambda? isP? (ƛ t) with isP? t
...                                | no ¬p = no λ { (islambda .t x) → ¬p x}
...                                | yes p = yes (islambda t p)
isLambda? isP? (t _⊢.· t₁) = no (λ ())
isLambda? isP? (_⊢.force t) = no (λ ())
isLambda? isP? (_⊢.delay t) = no (λ ())
isLambda? isP? (_⊢.con x) = no (λ ())
isLambda? isP? (constr i xs) = no (λ ())
isLambda? isP? (case t ts) = no (λ ())
isLambda? isP? (_⊢.builtin b) = no (λ ())
isLambda? isP? _⊢.error = no (λ ())

data isApp (X : Set) (P Q : Pred) : Pred where
  isapp : (l r : (X ⊢)) → P l → Q r → isApp X P Q (l · r)
isApp? : {X : Set} → { P Q : Pred} → Decidable P → Decidable Q → Decidable (isApp X P Q)
isApp? isP? isQ? (` x) = no (λ ())
isApp? isP? isQ? (ƛ t) = no (λ ())
isApp? isP? isQ? (t · t₁) with (isP? t) ×-dec (isQ? t₁)
...                                    | no ¬p = no λ { (isapp .t .t₁ x x₁) → ¬p (x , x₁)} 
...                                    | yes (p , q) = yes (isapp t t₁ p q)
isApp? isP? isQ? (force t) = no (λ ())
isApp? isP? isQ? (delay t) = no (λ ())
isApp? isP? isQ? (con x) = no (λ ())
isApp? isP? isQ? (constr i xs) = no (λ ())
isApp? isP? isQ? (case t ts) = no (λ ())
isApp? isP? isQ? (builtin b) = no (λ ())
isApp? isP? isQ? error = no (λ ())

data isForce (X : Set) (P : Pred) : Pred where
  isforce : (t : (X ⊢)) → P t → isForce X P (force t)
isForce? : {X : Set} → {P : Pred} → Decidable P → Decidable (isForce X P)
isForce? isP? (` x) = no (λ ())
isForce? isP? (ƛ t) = no (λ ())
isForce? isP? (t · t₁) = no (λ ())
isForce? isP? (force t) with isP? t
...                                  | no ¬p = no λ { (isforce .t x) → ¬p x} 
...                                  | yes p = yes (isforce t p)
isForce? isP? (delay t) = no (λ ())
isForce? isP? (con x) = no (λ ())
isForce? isP? (constr i xs) = no (λ ())
isForce? isP? (case t ts) = no (λ ())
isForce? isP? (builtin b) = no (λ ())
isForce? isP? error = no (λ ())


data isDelay (X : Set) (P : Pred) : Pred where
  isdelay : (t : (X ⊢)) → P t → isDelay X P (delay t)
isDelay? : {X : Set} → {P : Pred} → Decidable P → Decidable (isDelay X P)
isDelay? isP? (` x) = no (λ ())
isDelay? isP? (ƛ t) = no (λ ())
isDelay? isP? (t · t₁) = no (λ ())
isDelay? isP? (force t) = no (λ ())
isDelay? isP? (delay t) with isP? t
...                                  | yes p = yes (isdelay t p)
...                                  | no ¬p = no λ { (isdelay .t x) → ¬p x }
isDelay? isP? (con x) = no (λ ())
isDelay? isP? (constr i xs) = no (λ ())
isDelay? isP? (case t ts) = no (λ ())
isDelay? isP? (builtin b) = no (λ ())
isDelay? isP? error = no (λ ())

data isCon : Pred where
  iscon : (t : TmCon)  → isCon (con t)
isCon? : {X : Set} → Decidable (isCon) 
isCon? (` x) = no (λ _ → x)
isCon? (ƛ t) = no (λ ())
isCon? (t · t₁) = no (λ ())
isCon? (force t) = no (λ ())
isCon? (delay t) = no (λ ())
isCon? (con c) = yes (iscon c)
isCon? (constr i xs) = no (λ ())
isCon? (case t ts) = no (λ ())
isCon? (builtin b) = no (λ ())
isCon? error = no (λ ())

{-
data isConstr ????
-}

{-
data isCase ???
-}

data isBuiltin : Pred where
  isbuiltin : (b : Builtin) → isBuiltin (builtin b)
isBuiltin? : Decidable isBuiltin
isBuiltin? (` x) = no (λ _ → x)
isBuiltin? (ƛ t) = no (λ ())
isBuiltin? (t · t₁) = no (λ ())
isBuiltin? (force t) = no (λ ())
isBuiltin? (delay t) = no (λ ())
isBuiltin? (con x) = no (λ ())
isBuiltin? (constr i xs) = no (λ ())
isBuiltin? (case t ts) = no (λ ())
isBuiltin? (builtin b) = yes (isbuiltin b)
isBuiltin? error = no (λ ())

{- 
data isError (X : Set) : Pred where
  iserror : (t : X ⊢) → t ≟ error → isError X (error)
isError? : {X : Set} → Decidable (isError X)
isError? t = ?
-}
```
