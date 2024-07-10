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
-- Yes, I know, but for now...
{-# TERMINATING #-}
translation? : {X' : Set} {{ _ : DecEq X'}} →  {P Q : Pred} → ({X : Set} {{_ : DecEq X}} → Unary.Decidable (P {X})) → ({X : Set} {{_ : DecEq X}} → Unary.Decidable (Q {X})) → Binary.Decidable (Translation P Q {X'}) 
translation? isP? isQ? ast ast' with (isP? ast) ×-dec (isQ? ast')
... | yes (p , q) = yes (istranslation ast ast' p q)
translation? isP? isQ? (` x) ast' | no ¬pq with (` x) ≟ ast'
... | yes refl = yes var
... | no ¬x=x = no λ {
                (istranslation .(` x) .(ast') xx xxx) → ¬pq (xx , xxx);
                var → ¬x=x refl
                }
translation? isP? isQ? (ƛ ast) (ƛ ast') | no ¬pq with translation? isP? isQ? ast ast'
... | yes p = yes (ƛ p)
... | no ¬p = no (λ { (istranslation .(ƛ ast) .(ƛ ast') x x₁) → ¬pq (x , x₁) ; (ƛ pp) → ¬p pp })
translation? isP? isQ? (ƛ ast) (` x) | no ¬pq = no λ { (istranslation .(ƛ ast) .(` x) x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ƛ ast) (ast'' · ast''') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ƛ ast) (force ast'') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ƛ ast) (delay ast'') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ƛ ast) (con x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ƛ ast) (constr i xs) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ƛ ast) (case ast'' ts) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ƛ ast) (builtin b) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ƛ ast) error | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }

translation? isP? isQ? (ast · ast₁) (` x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ast · ast₁) (ƛ ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ast · ast₁) (ast' · ast'') | no ¬pq  with (translation? isP? isQ? ast ast') ×-dec (translation? isP? isQ? ast₁ ast'')
... | yes (p , q) = yes (app p q)
... | no ¬ppqq = no λ { (istranslation .(ast · ast₁) .(ast' · ast'') x x₁) → ¬pq (x , x₁) ; (app ppp ppp₁) → ¬ppqq (ppp , ppp₁)} 
translation? isP? isQ? (ast · ast₁) (force ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ast · ast₁) (delay ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ast · ast₁) (con x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ast · ast₁) (constr i xs) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ast · ast₁) (case ast' ts) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ast · ast₁) (builtin b) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (ast · ast₁) error | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }

translation? isP? isQ? (force ast) (` x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (force ast) (ƛ ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (force ast) (ast' · ast'') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (force ast) (force ast') | no ¬pq with translation? isP? isQ? ast ast'
... | yes p = yes (force p)
... | no ¬p = no λ { (istranslation .(force ast) .(force ast') x x₁) → ¬pq (x , x₁) ; (force pp) → ¬p pp }
translation? isP? isQ? (force ast) (delay ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (force ast) (con x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (force ast) (constr i xs) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (force ast) (case ast' ts) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (force ast) (builtin b) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (force ast) error | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }

translation? isP? isQ? (delay ast) (` x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (delay ast) (ƛ ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (delay ast) (ast' · ast'') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (delay ast) (force ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (delay ast) (delay ast') | no ¬pq with translation? isP? isQ? ast ast'
... | yes p = yes (delay p)
... | no ¬p = no λ { (istranslation .(delay ast) .(delay ast') x x₁) → ¬pq (x , x₁) ; (delay ppp) → ¬p ppp } 
translation? isP? isQ? (delay ast) (con x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (delay ast) (constr i xs) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (delay ast) (case ast' ts) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (delay ast) (builtin b) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (delay ast) error | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }

translation? isP? isQ? (con x) (` x₁) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (con x) (ƛ ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (con x) (ast' · ast'') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (con x) (force ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (con x) (delay ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (con x) (con x₁) | no ¬pq with x ≟ x₁
... | yes refl = yes con
... | no ¬p = no λ { (istranslation .(con x) .(con x₁) x₂ x₃) → ¬pq (x₂ , x₃) ; con → ¬p refl }
translation? isP? isQ? (con x) (constr i xs) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (con x) (case ast' ts) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (con x) (builtin b) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (con x) error | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }

translation? isP? isQ? (constr i xs) (` x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (constr i xs) (ƛ ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (constr i xs) (ast' · ast'') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (constr i xs) (force ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (constr i xs) (delay ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (constr i xs) (con x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (constr i xs) (constr i₁ xs₁) | no ¬pq with (i ≟ i₁) ×-dec (decPointwise (translation? isP? isQ?) xs xs₁)
... | yes (refl , pxs) = yes (constr pxs)
... | no ¬ixs = no λ { (istranslation .(constr i xs) .(constr i₁ xs₁) x x₁) → ¬pq (x , x₁) ; (constr x) → ¬ixs (refl , x) }
translation? isP? isQ? (constr i xs) (case ast' ts) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (constr i xs) (builtin b) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (constr i xs) error | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }

translation? isP? isQ? (case ast ts) (` x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (case ast ts) (ƛ ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (case ast ts) (ast' · ast'') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (case ast ts) (force ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (case ast ts) (delay ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (case ast ts) (con x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (case ast ts) (constr i xs) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (case ast ts) (case ast' ts₁) | no ¬pq with (translation? isP? isQ? ast ast') ×-dec (decPointwise (translation? isP? isQ?) ts ts₁)
... | yes ( pa , pts ) = yes (case pts pa)
... | no ¬papts = no λ { (istranslation .(case ast ts) .(case ast' ts₁) x x₁) → ¬pq (x , x₁) ; (case x xxx) → ¬papts (xxx , x) }
translation? isP? isQ? (case ast ts) (builtin b) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (case ast ts) error | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }

translation? isP? isQ? (builtin b) (` x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (builtin b) (ƛ ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (builtin b) (ast' · ast'') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (builtin b) (force ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (builtin b) (delay ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (builtin b) (con x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (builtin b) (constr i xs) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (builtin b) (case ast' ts) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? (builtin b) (builtin b₁) | no ¬pq with b ≟ b₁
... | yes refl = yes builtin
... | no ¬b=b₁ = no λ { (istranslation .(builtin b) .(builtin b₁) x x₁) → ¬pq (x , x₁) ; builtin → ¬b=b₁ refl }
translation? isP? isQ? (builtin b) error | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }

translation? isP? isQ? error (` x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? error (ƛ ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? error (ast' · ast'') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? error (force ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? error (delay ast') | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? error (con x) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? error (constr i xs) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? error (case ast' ts) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? error (builtin b) | no ¬pq = no λ { (istranslation _ _ x₁ x₂) → ¬pq (x₁ , x₂) }
translation? isP? isQ? error error | no ¬pq = yes error
```
