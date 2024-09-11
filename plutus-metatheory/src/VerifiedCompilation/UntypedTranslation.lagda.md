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
Relation = { X : Set } → {{_ : DecEq X}} → (X ⊢) → (X ⊢) → Set₁

data Translation (R : Relation) { X : Set } {{_ : DecEq X}} : (X ⊢) → (X ⊢) → Set₁ where
  istranslation : {ast ast' : X ⊢} → R ast ast' → Translation R ast ast'
  var : {x : X} → Translation R (` x) (` x) -- We assume we won't want to translate variables individually?
  ƛ   : {x x' : Maybe X ⊢}
           → Translation R x x'
           ----------------------
           →  Translation R (ƛ x) (ƛ x')
  app : {f t f' t' : X ⊢} →
        Translation R f f' →
        Translation R t t' →
        Translation R (f · t) (f' · t')
  force : {t t' : X ⊢} →
        Translation R t t' →
        Translation R (force t) (force t')
  delay : {t t' : X ⊢} →
        Translation R t t' →
        Translation R (delay t) (delay t')
  con : {tc : TmCon} → Translation R {X} (con tc) (con tc)
  constr : {xs xs' : List (X ⊢)} { n : ℕ }
                → Pointwise (Translation R) xs xs'
                  ------------------------
                → Translation R (constr n xs) (constr n xs')
  case : {p p' : X ⊢} {alts alts' : List (X ⊢)}
                → Pointwise (Translation R) alts alts' -- recursive translation for the other case patterns
                → Translation R p p'
                ------------------------
                → Translation R (case p alts) (case p' alts')
  builtin : {b : Builtin} → Translation R {X} (builtin b) (builtin b)
  error : Translation R {X} error error
```
For the decision procedure we have the rather dissapointing 110 lines to demonstrate to Agda that,
having determine that we aren't in the translation pattern, we are in fact, still not in the translation pattern
for each pair of term types.

```
open import Data.Product

-- Yes, I know, but for now...
{-# TERMINATING #-}
translation?
  : {X' : Set} {{ _ : DecEq X'}} {R : Relation}
  → ({ X : Set } {{ _ : DecEq X}} → Binary.Decidable (R {X}))
  → Binary.Decidable (Translation R {X'})
translation? {{de}} isR? ast ast' with (isR? ast ast')
... | yes p = yes (istranslation p)
translation? isR? (` x) ast' | no ¬p with (` x) ≟ ast'
... | yes refl = yes var
... | no ¬x=x = no λ {
                (istranslation xx) → ¬p xx;
                var → ¬x=x refl
                }
translation? isR? (ƛ ast) (ƛ ast') | no ¬p with translation? isR? ast ast'
... | yes p = yes (ƛ p)
... | no ¬pp = no (λ { (istranslation x) → ¬p x ; (ƛ xxx) → ¬pp xxx})
translation? isR? (ƛ ast) (` x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ƛ ast) (ast'' · ast''') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ƛ ast) (force ast'') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ƛ ast) (delay ast'') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ƛ ast) (con x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ƛ ast) (constr i xs) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ƛ ast) (case ast'' ts) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ƛ ast) (builtin b) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ƛ ast) error | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }

translation? isR? (ast · ast₁) (` x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ast · ast₁) (ƛ ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ast · ast₁) (ast' · ast'') | no ¬p  with (translation? isR? ast ast') ×-dec (translation? isR? ast₁ ast'')
... | yes (p , q) = yes (app p q)
... | no ¬ppqq = no λ { (istranslation x) → ¬p x ; (app ppp ppp₁) → ¬ppqq (ppp , ppp₁)}
translation? isR? (ast · ast₁) (force ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ast · ast₁) (delay ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ast · ast₁) (con x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ast · ast₁) (constr i xs) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ast · ast₁) (case ast' ts) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ast · ast₁) (builtin b) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (ast · ast₁) error | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }

translation? isR? (force ast) (` x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (force ast) (ƛ ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (force ast) (ast' · ast'') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (force ast) (force ast') | no ¬p with translation? isR? ast ast'
... | yes p = yes (force p)
... | no ¬pp = no λ { (istranslation x) → ¬p x ; (force xxx) → ¬pp xxx }
translation? isR? (force ast) (delay ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (force ast) (con x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (force ast) (constr i xs) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (force ast) (case ast' ts) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (force ast) (builtin b) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (force ast) error | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }

translation? isR? (delay ast) (` x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (delay ast) (ƛ ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (delay ast) (ast' · ast'') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (delay ast) (force ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (delay ast) (delay ast') | no ¬p with translation? isR? ast ast'
... | yes p = yes (delay p)
... | no ¬pp = no λ { (istranslation x) → ¬p x ; (delay xxx) → ¬pp xxx }
translation? isR? (delay ast) (con x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (delay ast) (constr i xs) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (delay ast) (case ast' ts) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (delay ast) (builtin b) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (delay ast) error | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }

translation? isR? (con x) (` x₁) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (con x) (ƛ ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (con x) (ast' · ast'') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (con x) (force ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (con x) (delay ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (con x) (con x₁) | no ¬p with x ≟ x₁
... | yes refl = yes con
... | no ¬x≟x₁ = no λ { (istranslation xx) → ¬p xx ; con → ¬x≟x₁ refl }
translation? isR? (con x) (constr i xs) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (con x) (case ast' ts) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (con x) (builtin b) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (con x) error | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }

translation? isR? (constr i xs) (` x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (constr i xs) (ƛ ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (constr i xs) (ast' · ast'') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (constr i xs) (force ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (constr i xs) (delay ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (constr i xs) (con x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (constr i xs) (constr i₁ xs₁) | no ¬p with (i ≟ i₁) ×-dec (decPointwise (translation? isR?) xs xs₁)
... | yes (refl , pxs) = yes (constr pxs)
... | no ¬ixs = no λ { (istranslation x) → ¬p x ; (constr x) → ¬ixs (refl , x) }
translation? isR? (constr i xs) (case ast' ts) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (constr i xs) (builtin b) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (constr i xs) error | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }

translation? isR? (case ast ts) (` x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (case ast ts) (ƛ ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (case ast ts) (ast' · ast'') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (case ast ts) (force ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (case ast ts) (delay ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (case ast ts) (con x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (case ast ts) (constr i xs) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (case ast ts) (case ast' ts₁) | no ¬p with (translation? isR? ast ast') ×-dec (decPointwise (translation? isR?) ts ts₁)
... | yes ( pa , pts ) = yes (case pts pa)
... | no ¬papts = no λ { (istranslation x) → ¬p x ; (case x xxx) → ¬papts (xxx , x) }
translation? isR? (case ast ts) (builtin b) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (case ast ts) error | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }

translation? isR? (builtin b) (` x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (builtin b) (ƛ ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (builtin b) (ast' · ast'') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (builtin b) (force ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (builtin b) (delay ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (builtin b) (con x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (builtin b) (constr i xs) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (builtin b) (case ast' ts) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? (builtin b) (builtin b₁) | no ¬p with b ≟ b₁
... | yes refl = yes builtin
... | no ¬b=b₁ = no λ { (istranslation x) → ¬p x ; builtin → ¬b=b₁ refl }
translation? isR? (builtin b) error | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }

translation? isR? error (` x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? error (ƛ ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? error (ast' · ast'') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? error (force ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? error (delay ast') | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? error (con x) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? error (constr i xs) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? error (case ast' ts) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? error (builtin b) | no ¬p = no λ { (istranslation x₁) → ¬p x₁ }
translation? isR? error error | no ¬p = yes error
```
# Relations between Translations

These functions can be useful when showing equivilence etc. between translation relations.

```
variable
  R S : Relation
  X : Set
  x x' : X ⊢
  xs xs' : List (X ⊢)

convert-pointwise : {{deX : DecEq X}} → (∀ {Y : Set} {{deY : DecEq Y}} {y y' : Y ⊢} → R {{deY}} y y' → S {{deY}} y y') → (Pointwise (R {{deX}}) xs xs' → Pointwise (S {{deX}}) xs xs')
convert-pointwise f Pointwise.[] = Pointwise.[]
convert-pointwise {R = R} {S = S} f (x∼y Pointwise.∷ p) = f x∼y Pointwise.∷ convert-pointwise {R =  R} {S = S} f p

{-# TERMINATING #-}
convert : {{deX : DecEq X}} → (∀ {Y : Set} {{deY : DecEq Y}} {y y' : Y ⊢} → R y y' → S y y') → (Translation R {{deX}} x x' → Translation S {{deX}} x x')
convert f (Translation.istranslation xx') = Translation.istranslation (f xx')
convert f Translation.var = Translation.var
convert f (Translation.ƛ xx') = Translation.ƛ (convert f xx')
convert f (Translation.app xx' xx'') = Translation.app (convert f xx') (convert f xx'')
convert f (Translation.force xx') = Translation.force (convert f xx')
convert f (Translation.delay xx') = Translation.delay (convert f xx')
convert f Translation.con = Translation.con
convert {R = R} {S = S} f (Translation.constr x) = Translation.constr (convert-pointwise {R = Translation R} {S = Translation S} (convert f) x)
convert f (case Pointwise.[] xx') = case Pointwise.[] (convert f xx')
convert {R = R} {S = S} f (case (x∼y Pointwise.∷ x) xx') = Translation.case (convert-pointwise {R = Translation R} {S = Translation S} (convert f) (x∼y Pointwise.∷ x)) (convert f xx')
convert f Translation.builtin = Translation.builtin
convert f Translation.error = Translation.error

pointwise-reflexive : (∀ {X : Set} {{deX : DecEq X}} {x : X ⊢} → Translation R {{deX}} x x) → (∀ {X : Set} {{deX : DecEq X}} {xs : List (X ⊢)} → Pointwise (Translation R {{deX}}) xs xs)
pointwise-reflexive f {xs = List.[]} = Pointwise.[]
pointwise-reflexive f {xs = x List.∷ xs} = f Pointwise.∷ pointwise-reflexive f

{-# TERMINATING #-}
reflexive : {{deX : DecEq X}} → Translation R {{deX}} x x
reflexive {x = ` x} = var
reflexive {x = ƛ x} = ƛ reflexive
reflexive {x = x · x₁} = app reflexive reflexive
reflexive {x = force x} = force reflexive
reflexive {x = delay x} = delay reflexive
reflexive {x = con x} = con
reflexive {x = constr i xs} = constr (pointwise-reflexive reflexive)
reflexive {x = case x ts} = case (pointwise-reflexive reflexive) reflexive
reflexive {x = builtin b} = builtin
reflexive {x = error} = error
```
