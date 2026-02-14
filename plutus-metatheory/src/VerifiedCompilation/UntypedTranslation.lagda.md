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
open import RawU using (TmCon; tmCon; TyTag; ⟦_⟧tag; decTagCon; tmCon2TagCon)
open import Data.List using (List; [_])
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; eq?)
open import Builtin using (Builtin)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Untyped.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.Certificate using (ProofOrCE; proof; ce; decToPCE; MatchOrCE; SimplifierTag)
open import Data.Sum using (_⊎_;inj₁; inj₂)

```
The generic type of a Translation is that it matches one (or more) patterns on the left to one
(or more) patterns on the right. If there are decision procedures to identify those patterns,
we can build a decision procedure to apply them recursivley down the AST structure.

```
Relation = { X : ℕ } → (X ⊢) → (X ⊢) → Set

data Translation (R : Relation) { X : ℕ } : (X ⊢) → (X ⊢) → Set

data TransMatch (R : Relation) { X : ℕ } : (X ⊢) → (X ⊢) → Set where
  var : {x : Fin X} → TransMatch R (` x) (` x) -- We assume we won't want to translate variables individually?
  ƛ   : {x x' : suc X ⊢}
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

untypedIx : {X : ℕ} → X ⊢ → ℕ
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

matchIx : {R : Relation}{X : ℕ}{a b : X ⊢} → TransMatch R a b → untypedIx a ≡ untypedIx b
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
  : {X' : ℕ} {R : Relation}
  → SimplifierTag
  → ({ X : ℕ } → MatchOrCE (R {X}))
  → (p q : X' ⊢) → ProofOrCE (Translation R {X'} p q)

decPointwiseTranslation?
  : {X' : ℕ} {R : Relation}
  → SimplifierTag
  → ({ X : ℕ } → MatchOrCE (R {X}))
  → (p q : List (X' ⊢)) → ProofOrCE (Pointwise (Translation R {X'}) p q)
decPointwiseTranslation? _ _ [] [] = proof Pointwise.[]
decPointwiseTranslation? {X' = X'} tag isR? [] (x ∷ ys) = ce (λ ()) {X = List (Fin X')} tag [] (x ∷ ys)
decPointwiseTranslation? {X' = X'} tag isR? (x ∷ xs) [] = ce (λ ()) {X' = List (Fin X')} tag (x ∷ xs) []
decPointwiseTranslation? tag isR? (x ∷ xs) (y ∷ ys)
    with translation? tag isR? x y | decPointwiseTranslation? tag isR? xs ys
... | proof p | proof q = proof (p Pointwise.∷ q)
... | proof _ | ce ¬p t before after = ce (λ { (x∼y Pointwise.∷ x) → ¬p x }) t before after
... | ce ¬p t before after | _     = ce (λ { (x∼y Pointwise.∷ x) → ¬p x∼y }) t before after

translation? {_} tag isR? ast ast' with (untypedIx ast) Data.Nat.≟ (untypedIx ast')
translation? {X} tag isR? (` x) (` x₁) | yes _ with Data.Fin._≟_ x x₁
... | yes refl = proof (match var)
... | no x≠x₁ with isR? {X} (` x) (` x₁)
...   | proof p = proof (istranslation p)
...   | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match var) → x≠x₁ refl }) t b a
translation? {_} tag isR? (ƛ ast) (ƛ ast') | yes _ with translation? tag isR? ast ast'
...                  | proof t = proof (match (ƛ t))
...                  | ce ¬tr t b a with isR? (ƛ ast) (ƛ ast')
...                               | proof p = proof (istranslation p)
...                               | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match (ƛ tr)) → ¬tr tr }) t b a
translation? {_} tag isR? (ast · ast₁) (ast' · ast₁') | yes _ with (translation? tag isR? ast ast')
translation? {_} tag isR? (ast · ast₁) (ast' · ast₁') | yes _ | ce ¬p t b a with isR? (ast · ast₁) (ast' · ast₁')
translation? {_} tag isR? (ast · ast₁) (ast' · ast₁') | yes _ | ce ¬p t b a | proof p = proof (istranslation p)
translation? {_} tag isR? (ast · ast₁) (ast' · ast₁') | yes _ | ce ¬tr _ _ _ | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match (app x x₁)) → ¬tr x }) t b a
translation? {_} tag isR? (ast · ast₁) (ast' · ast₁') | yes _ | proof l with (translation? tag isR? ast₁ ast₁')
translation? {_} tag isR? (ast · ast₁) (ast' · ast₁') | yes _ | proof l | proof r = proof (match (app l r))
translation? {_} tag isR? (ast · ast₁) (ast' · ast₁') | yes _ | proof l | ce ¬p t b a with isR? (ast · ast₁) (ast' · ast₁')
translation? {_} tag isR? (ast · ast₁) (ast' · ast₁') | yes _ | proof l | ce ¬p t b a | proof p = proof (istranslation p)
translation? {_} tag isR? (ast · ast₁) (ast' · ast₁') | yes _ | proof l | ce ¬tr _ _ _ | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match (app x x₁)) → ¬tr x₁ }) t b a
translation? {_} tag isR? (force ast) (force ast') | yes _ with translation? tag isR? ast ast'
...                  | proof t = proof (match (force t))
...                  | ce ¬tr t b a with isR? (force ast) (force ast')
...                               | proof p = proof (istranslation p)
...                               |  ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match (force x)) → ¬tr x }) t b a
translation? {_} tag isR? (delay ast) (delay ast') | yes _ with translation? tag isR? ast ast'
...                  | proof t = proof (match (delay t))
...                  | ce ¬tr t b a with isR? (delay ast) (delay ast')
...                               | proof p = proof (istranslation p)
...                               | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match (delay x)) → ¬tr x }) t b a
translation? {X} tag isR? (con x) (con x₁) | yes _ with x ≟ x₁
...                  | yes refl = proof (match con)
...                  | no x≠x₁ with isR? {X} (con x) (con x₁)
...                                   | proof p = proof (istranslation p)
...                                   | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match con) → x≠x₁ refl }) t b a
translation? {_} tag isR? (constr i xs) (constr i₁ xs₁) | yes _ with (decToPCE tag (i ≟ i₁) {constr i xs} {constr i₁ xs₁})
...                  | ce ¬i≡i₁ t b a with isR? (constr i xs) (constr i₁ xs₁)
...                                    | proof p = proof (istranslation p)
...                                    | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match (constr x)) → ¬i≡i₁ refl }) t b a
translation? {_} tag isR? (constr i xs) (constr i₁ xs₁) | yes _ | proof refl with (decPointwiseTranslation? tag isR? xs xs₁)
...                                    | proof t = proof (match (constr t))
...                                    | ce ¬pp t b a with isR? (constr i xs) (constr i₁ xs₁)
...                                                | proof p = proof (istranslation p)
...                                                | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match (constr x)) → ¬pp x}) t b a
translation? {_} tag isR? (case ast ts) (case ast' ts₁) | yes _ with (translation? tag isR? ast ast')
...                  | ce ¬tr t b a with isR? (case ast ts) (case ast' ts₁)
...                                    | proof p = proof (istranslation p)
...                                    | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match (case x x₁)) → ¬tr x₁}) t b a
translation? {_} tag isR? (case ast ts) (case ast' ts₁) | yes _ | proof pa with (decPointwiseTranslation? tag isR? ts ts₁)
...                                    | proof t = proof (match (case t pa))
...                                    | ce ¬tr t b a with isR? (case ast ts) (case ast' ts₁)
...                                           | proof p = proof (istranslation p)
...                                           | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match (case x x₁)) → ¬tr x}) t b a
translation? {X} tag isR? (builtin b) (builtin b₁) | yes _ with b ≟ b₁
... | yes refl = proof (match builtin)
... | no b≠b₁ with isR? {X} (builtin b) (builtin b₁)
...                  | proof p = proof (istranslation p)
...                  | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match builtin) → b≠b₁ refl }) t b a
translation? {_} tag isR? error error | yes _ = proof (match error)
translation? {_} tag isR? ast ast' | no ast≠ast' with isR? ast ast'
... | proof p = proof (istranslation p)
... | ce ¬p t b a = ce (λ { (istranslation x) → ¬p x ; (match tm) → ast≠ast' (matchIx tm)} ) t b a

```
# Relations between Translations

These functions can be useful when showing equivilence etc. between translation relations.

```
variable
  R S : Relation
  X : ℕ
  x x' : X ⊢
  xs xs' : List (X ⊢)

convert-pointwise : (∀ {Y : ℕ} {y y' : Y ⊢} → R y y' → S y y') → (Pointwise R xs xs' → Pointwise S xs xs')
convert-pointwise f Pointwise.[] = Pointwise.[]
convert-pointwise {R = R} {S = S} f (x∼y Pointwise.∷ p) = f x∼y Pointwise.∷ convert-pointwise {R =  R} {S = S} f p


{-# TERMINATING #-}
convert : (∀ {Y : ℕ} {y y' : Y ⊢} → R y y' → S y y') → (Translation R x x' → Translation S x x')
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

pointwise-reflexive : (∀ {X : ℕ} {x : X ⊢} → Translation R x x) → (∀ {X : ℕ} {xs : List (X ⊢)} → Pointwise (Translation R) xs xs)
pointwise-reflexive f {xs = List.[]} = Pointwise.[]
pointwise-reflexive f {xs = x List.∷ xs} = f Pointwise.∷ pointwise-reflexive f

{-# TERMINATING #-}
reflexive : Translation R x x
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
