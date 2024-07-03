---
title: VerifiedCompilation.UntypedTranslation
layout: page
---
# Generic Translation Relations for Untyped Plutus Core

```
module VerifiedCompilation.UntypedTranslation where

open import Untyped using (_⊢; `; ƛ; case; constr; _·_; force; delay; con; builtin; error)
import Relation.Unary as Unary using (Decidable)
import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary.Product using (_×-dec_)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import VerifiedCompilation.UntypedViews using (Pred; ListPred)
open import Utils as U using (Maybe)
open import RawU using (TmCon; tmCon; decTag; TyTag; ⟦_⟧tag; decTagCon; tmCon2TagCon)
open import Data.List using (List; [_])
open import Data.Nat using (ℕ)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Builtin using (Builtin)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import VerifiedCompilation.Equality using (DecEq; _≟_; decPointwise)
```
The generic type of a Translation is that it matches one (or more) patterns on the left to one
(or more) patterns on the right. If there are decision procedures to identify those patterns,
we can build a decision procedure to apply them recursivley down the AST structure. 

```
data Translation (P Q : Pred) : { X' : Set } → (X' ⊢) → (X' ⊢) → Set₁ where
  istranslation :  { X' : Set } → (ast ast' : X' ⊢) → P ast → Q ast' → Translation P Q ast ast'
  var : {X : Set} → {x : X} → Translation P Q (` x) (` x) -- We assume we won't want to translate variables individually?
  ƛ   : {X : Set} →  {x x' : Maybe X ⊢}
           → Translation P Q x x'
           ----------------------
           →  Translation P Q (ƛ x) (ƛ x') 
  app : {X : Set} → {f t f' t' : X ⊢} →
        Translation P Q f f' →
        Translation P Q t t' →
        Translation P Q (f · t) (f' · t')
  force : {X : Set} → {t t' : X ⊢} →
        Translation P Q t t' →
        Translation P Q (force t) (force t')  
  delay : {X : Set} → {t t' : X ⊢} →
        Translation P Q t t' →
        Translation P Q (delay t) (delay t') 
  con : {X : Set} → {tc : TmCon} → Translation P Q {X} (con tc) (con tc)
  constr : {X : Set} → {xs xs' : List (X ⊢)} { n : ℕ }
                → Pointwise (Translation P Q) xs xs'
                  ------------------------
                → Translation P Q (constr n xs) (constr n xs')
  case :  {X : Set} → {p p' : X ⊢} {alts alts' : List (X ⊢)}
                → Pointwise (Translation P Q) alts alts' -- recursive translation for the other case patterns
                → Translation P Q p p'
                ------------------------
                → Translation P Q (case p alts) (case p' alts')
  builtin : {X : Set} → {b : Builtin} → Translation P Q {X} (builtin b) (builtin b)
  error : {X : Set} → Translation P Q {X} error error
```
For the decision procedure we have the rather dissapointing 110 lines to demonstrate to Agda that,
having determine that we aren't in the translation pattern, we are in fact, still not in the translation pattern
for each pair of term types. 
```
translation? : {X' : Set} {{ _ : DecEq X'}} →  {P Q : Pred} → (∀ {X} → Unary.Decidable (P {X})) → (∀ {X} → Unary.Decidable (Q {X})) → Binary.Decidable (Translation P Q {X'}) 
translation? isP? isQ? ast ast' with (isP? ast) ×-dec (isQ? ast')
... | yes (p , q) = yes (istranslation ast ast' p q)
... | no ¬p = {!!}
translation? isP? isQ? (` x) ast' | no ¬pq with (ast' ≟ (` x))
... | yes refl = yes var
... | no ¬x=x = no λ { (istranslation (` x₂) .ast' x x₁) → ¬pq (x , x₁) ;
                                var → ¬x=x refl } 
translation? {X'} isP? isQ? (ƛ ast₂) (ƛ ast'₂) | no ¬pq with translation? {Maybe X'} isP? isQ? ast₂ ast'₂
... | yes ppp = yes (ƛ ppp)
... | no ¬ppp = {!!}
translation? isP? isQ? _ _ = {!!}
```
