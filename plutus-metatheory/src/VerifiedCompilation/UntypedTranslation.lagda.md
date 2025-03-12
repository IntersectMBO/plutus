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
open import Relation.Nullary using (_×-dec_)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import VerifiedCompilation.UntypedViews using (Pred; ListPred)
open import Utils as U using (Maybe)
open import RawU using (TmCon; tmCon; decTag; TyTag; ⟦_⟧tag; decTagCon; tmCon2TagCon)
open import Data.List using (List; [_])
open import Data.Nat using (ℕ; eq?)
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

data Translation (R : Relation) { X : Set } {{_ : DecEq X}} : (X ⊢) → (X ⊢) → Set₁

data TransMatch (R : Relation) { X : Set } {{_ : DecEq X}} : (X ⊢) → (X ⊢) → Set₁ where
  var : {x : X} → TransMatch R (` x) (` x) -- We assume we won't want to translate variables individually?
  ƛ   : {x x' : Maybe X ⊢}
           → Translation R x x'
           ----------------------
           → TransMatch R (ƛ x) (ƛ x')
  app : {f t f' t' : X ⊢} →
        Translation R f f' →
        Translation R t t' →
        TransMatch R (f · t) (f' · t')
  force : {t t' : X ⊢} →
        Translation R t t' →
        TransMatch R (force t) (force t')
  delay : {t t' : X ⊢} →
        Translation R t t' →
        TransMatch R (delay t) (delay t')
  con : {tc : TmCon} → TransMatch R {X} (con tc) (con tc)
  constr : {xs xs' : List (X ⊢)} { n : ℕ }
                → Pointwise (Translation R) xs xs'
                  ------------------------
                → TransMatch R (constr n xs) (constr n xs')
  case : {p p' : X ⊢} {alts alts' : List (X ⊢)}
                → Pointwise (Translation R) alts alts' -- recursive translation for the other case patterns
                → Translation R p p'
                ------------------------
                → TransMatch R (case p alts) (case p' alts')
  builtin : {b : Builtin} → TransMatch R {X} (builtin b) (builtin b)
  error : TransMatch R {X} error error


data Translation R {X} where
  istranslation : {ast ast' : X ⊢} → R ast ast' → Translation R ast ast'
  match : {ast ast' : X ⊢} → TransMatch R ast ast' → Translation R ast ast'
```
For the decision procedure we have the rather dissapointing 110 lines to demonstrate to Agda that,
having determined that we aren't in the translation pattern, we are in fact, still not in the translation pattern
for each pair of term types.

```
open import Data.Product

untypedIx : {X : Set} → X ⊢ → ℕ
untypedIx (` x) = 1
untypedIx (ƛ t) = 2
untypedIx (t · t₁) = 3
untypedIx (force t) = 4
untypedIx (delay t) = 5
untypedIx (con x) = 6
untypedIx (constr i xs) = 7
untypedIx (case t ts) = 8
untypedIx (builtin b) = 9
untypedIx error = 10

matchIx : {R : Relation}{X : Set}{{ _ : DecEq X}}{a b : X ⊢} → TransMatch R a b → untypedIx a ≡ untypedIx b
matchIx var = refl
matchIx (ƛ x) = refl
matchIx (app x x₁) = refl
matchIx (force x) = refl
matchIx (delay x) = refl
matchIx con = refl
matchIx (constr x) = refl
matchIx (case x x₁) = refl
matchIx builtin = refl
matchIx error = refl

translation?
  : {X' : Set} {{ _ : DecEq X'}} {R : Relation}
  → ({ X : Set } {{ _ : DecEq X}} → Binary.Decidable (R {X}))
  → Binary.Decidable (Translation R {X'})

decPointwiseTranslation?
  : {X' : Set} {{ _ : DecEq X'}} {R : Relation}
  → ({ X : Set } {{ _ : DecEq X}} → Binary.Decidable (R {X}))
  → Binary.Decidable (Pointwise (Translation R {X'}))
decPointwiseTranslation? isR? [] [] = yes Pointwise.[]
decPointwiseTranslation? isR? [] (x ∷ ys) = no (λ ())
decPointwiseTranslation? isR? (x ∷ xs) [] = no (λ ())
decPointwiseTranslation? isR? (x ∷ xs) (y ∷ ys)
    with translation? isR? x y | decPointwiseTranslation? isR? xs ys
... | yes p | yes q = yes (p Pointwise.∷ q)
... | yes _ | no ¬q = no λ where (_ Pointwise.∷ xs~ys) → ¬q xs~ys
... | no ¬p | _     = no λ where (x∼y Pointwise.∷ _) → ¬p x∼y

translation? {_} ⦃ de ⦄ isR? ast ast' with (untypedIx ast) Data.Nat.≟ (untypedIx ast')
translation? {X} ⦃ de ⦄ isR? (` x) (` x₁) | yes _ with x ≟ x₁
... | yes refl = yes (match var)
... | no x≠x₁ with isR? {X} (` x) (` x₁)
...                  | yes p = yes (istranslation p)
...                  | no ¬p = no λ { (istranslation x) → ¬p x ; (match var) → x≠x₁ refl }
translation? {_} ⦃ de ⦄ isR? (ƛ ast) (ƛ ast') | yes _ with translation? isR? ast ast'
...                  | yes t = yes (match (ƛ t))
...                  | no ¬t with isR? (ƛ ast) (ƛ ast')
...                               | yes p = yes (istranslation p)
...                               | no ¬p = no λ { (istranslation x) → ¬p x ; (match (ƛ x)) → ¬t x }
translation? {_} ⦃ de ⦄ isR? (ast · ast₁) (ast' · ast₁') | yes _ with (translation? isR? ast ast') ×-dec (translation? isR? ast₁ ast₁')
...                                                  | yes t = yes (match (app (t .proj₁) (t .proj₂)))
...                                                  | no ¬t with isR? (ast · ast₁) (ast' · ast₁')
...                                                                | yes p = yes (istranslation p)
...                                                                | no ¬p = no λ { (istranslation x) → ¬p x ; (match (app x x₁)) → ¬t (x , x₁) }
translation? {_} ⦃ de ⦄ isR? (force ast) (force ast') | yes _ with translation? isR? ast ast'
...                  | yes t = yes (match (force t))
...                  | no ¬t with isR? (force ast) (force ast')
...                               | yes p = yes (istranslation p)
...                               | no ¬p = no λ { (istranslation x) → ¬p x ; (match (force x)) → ¬t x }
translation? {_} ⦃ de ⦄ isR? (delay ast) (delay ast') | yes _ with translation? isR? ast ast'
...                  | yes t = yes (match (delay t))
...                  | no ¬t with isR? (delay ast) (delay ast')
...                               | yes p = yes (istranslation p)
...                               | no ¬p = no λ { (istranslation x) → ¬p x ; (match (delay x)) → ¬t x }
translation? {X} ⦃ de ⦄ isR? (con x) (con x₁) | yes _ with x ≟ x₁
...                  | yes refl = yes (match con)
...                  | no x≠x₁ with isR? {X} (con x) (con x₁)
...                                   | yes p = yes (istranslation p)
...                                   | no ¬p = no λ { (istranslation x) → ¬p x ; (match con) → x≠x₁ refl }
translation? {_} ⦃ de ⦄ isR? (constr i xs) (constr i₁ xs₁) | yes _ with (i ≟ i₁) ×-dec (decPointwiseTranslation? isR? xs xs₁)
...                  | yes (refl , snd) = yes (match (constr snd))
...                  | no ¬t with isR? (constr i xs) (constr i₁ xs₁)
...                                   | yes p = yes (istranslation p)
...                                   | no ¬p = no λ { (istranslation x) → ¬p x ; (match (constr x)) → ¬t (refl , x)}
translation? {_} ⦃ de ⦄ isR? (case ast ts) (case ast' ts₁) | yes _ with (translation? isR? ast ast') ×-dec (decPointwiseTranslation? isR? ts ts₁)
... | yes ( pa , pts ) = yes (match (case pts pa))
... | no ¬papts with isR? (case ast ts) (case ast' ts₁)
...       | yes p = yes (istranslation p)
...       | no ¬p = no λ { (istranslation x) → ¬p x ; (match (case x xxx)) → ¬papts (xxx , x) }
translation? {X} ⦃ de ⦄ isR? (builtin b) (builtin b₁) | yes _ with b ≟ b₁
... | yes refl = yes (match builtin)
... | no b≠b₁ with isR? {X} (builtin b) (builtin b₁)
...                  | yes p = yes (istranslation p)
...                  | no ¬p = no λ { (istranslation x) → ¬p x ; (match builtin) → b≠b₁ refl }
translation? {_} ⦃ de ⦄ isR? error error | yes _ = yes (match error)
translation? {_} ⦃ de ⦄ isR? ast ast' | no ast≠ast' with isR? ast ast'
...                  | yes p = yes (istranslation p)
...                  | no ¬p = no λ { (istranslation x) → ¬p x ; (match tm) → ast≠ast' (matchIx tm) }

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
convert f (match var) = match var
convert f (match (ƛ x)) = match (ƛ (convert f x))
convert f (match (app x x₁)) = match (app (convert f x) (convert f x₁))
convert f (match (force x)) = match (force (convert f x))
convert f (match (delay x)) = match (delay (convert f x))
convert f (match con) = match con
convert {R = R} {S = S} f (match (constr x)) = match (constr (convert-pointwise {R = Translation R} {S = Translation S} (convert f) x))
convert f (match (case Pointwise.[] xx')) = match (case Pointwise.[] (convert f xx'))
convert {R = R} {S = S} f (match (case (x∼y Pointwise.∷ x) x₁)) = match (case (convert-pointwise {R = Translation R} {S = Translation S} (convert f) (x∼y Pointwise.∷ x)) (convert f x₁))
convert f (match builtin) = match builtin
convert f (match error) = match error

pointwise-reflexive : (∀ {X : Set} {{deX : DecEq X}} {x : X ⊢} → Translation R {{deX}} x x) → (∀ {X : Set} {{deX : DecEq X}} {xs : List (X ⊢)} → Pointwise (Translation R {{deX}}) xs xs)
pointwise-reflexive f {xs = List.[]} = Pointwise.[]
pointwise-reflexive f {xs = x List.∷ xs} = f Pointwise.∷ pointwise-reflexive f

{-# TERMINATING #-}
reflexive : {{deX : DecEq X}} → Translation R {{deX}} x x
reflexive {x = ` x} = match var
reflexive {x = ƛ x} = match (ƛ reflexive)
reflexive {x = x · x₁} = match (app reflexive reflexive)
reflexive {x = force x} = match (force reflexive)
reflexive {x = delay x} = match (delay reflexive)
reflexive {x = con x} = match con
reflexive {x = constr i xs} = match (constr (pointwise-reflexive reflexive))
reflexive {x = case x ts} = match (case (pointwise-reflexive reflexive) reflexive)
reflexive {x = builtin b} = match builtin
reflexive {x = error} = match error

```
