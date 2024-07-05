---
title: VerifiedCompilation.Equality
layout: page
---
# Verified Compilation Equality
```
module VerifiedCompilation.Equality where
```

## Decidable Equivalence

We need to determine if two terms refer to the same variable, so we need decidable
equivalence on variables, which are really de Brujin numbers encoded using Maybe.

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; isEquivalence; cong)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import RawU using (TmCon; tmCon; decTag; TyTag; ⟦_⟧tag; decTagCon; tmCon2TagCon)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Builtin.Constant.AtomicType using (AtomicTyCon; decAtomicTyCon; ⟦_⟧at)
open import Agda.Builtin.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-≡⇒≡; ≡⇒Pointwise-≡)
open import Data.List.Properties using (≡-dec)
open import Relation.Binary.Core using (REL)
open import Level using (Level)
open import Builtin using (Builtin; decBuiltin)
open import Builtin.Signature using (_⊢♯)
import Data.Nat.Properties using (_≟_)
open import Untyped using (_⊢; `; ƛ; case; constr; _·_; force; delay; con; builtin; error)
import Relation.Unary as Unary using (Decidable)
import Relation.Binary.Definitions as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_,_)
open import Relation.Nullary.Product using (_×-dec_)
open import Utils as U using (Maybe; nothing; just; Either)
import Data.List.Properties as LP using (≡-dec)

record DecEq (A : Set) : Set where
  field _≟_ : DecidableEquality A
open DecEq {{...}} public

postulate
   -- This is fairly straightforward to define but it depends on
   -- DecidableEquality over various Agda builtin types, which is
   -- easy to do but should be in the standard library *somewhere*??
   dec-⟦_⟧tag : ( t : TyTag ) → DecidableEquality ⟦ t ⟧tag
   decEq-TmCon : DecidableEquality TmCon

{-
decEq-TmCon (tmCon t1 v1) (tmCon t2 v2) with decTag t1 t2 | dec-⟦_⟧tag v1 v2
...                                                                 | no ¬p   | _         = no {!!}
...                                                                 | yes refl | no ¬p  = {!!}
...                                                                 | yes refl | yes p  = yes {!!}
-}
   
```
# Pointwise Decisions

At some points we will want to show that one list of AST elements is a valid translation
of another list of AST elements by showing the `n`th element of one is a translation of the
`n`th element of the other, pointwise. 

```
decPointwise : {l₁ l₂ : Level} { A B : Set l₁ } { _~_ : A → B → Set l₂} → Binary.Decidable _~_ → Binary.Decidable (Pointwise _~_)
decPointwise dec [] [] = yes Pointwise.[]
decPointwise dec [] (x ∷ ys) = no (λ ())
decPointwise dec (x ∷ xs) [] = no (λ ())
decPointwise dec (x ∷ xs) (y ∷ ys) with dec x y | decPointwise dec xs ys
... | yes p | yes q = yes (p Pointwise.∷ q) 
... | yes _ | no ¬q = no λ where (_ Pointwise.∷ xs~ys) → ¬q xs~ys
... | no ¬p | _     = no λ where (x∼y Pointwise.∷ _) → ¬p x∼y
```

## Decidable Equality Instances 

Creating Instance declarations for various Decidable Equality functions to be used
when creating translation decision procedures.

```
decEq-⊢ : ∀{X} {{_ : DecEq X}} → DecidableEquality (X ⊢)

instance
  DecEq-Maybe : ∀{A} {{_ : DecEq A}} → DecEq (Maybe A)
  DecEq-Maybe ._≟_ = M.≡-dec _≟_
    where import Data.Maybe.Properties as M

  DecAtomicTyCon : DecEq AtomicTyCon
  DecAtomicTyCon ._≟_ = decAtomicTyCon

  DecEq-TmCon : DecEq TmCon
  DecEq-TmCon ._≟_ = decEq-TmCon

  DecEq-⊢ : ∀{X} {{_ : DecEq X}} → DecEq (X ⊢)
  DecEq-⊢ ._≟_ = decEq-⊢

  DecEq-List-⊢ : ∀{X} {{_ : DecEq X}} → DecEq (List (X ⊢))
  DecEq-List-⊢ ._≟_ = LP.≡-dec decEq-⊢

  DecEq-Builtin : DecEq Builtin
  DecEq-Builtin ._≟_ = decBuiltin

  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ ._≟_ = Data.Nat.Properties._≟_

-- FIXME: this shouldn't be needed? It is the mutual recursion with list equality that requires it. 
{-# TERMINATING #-}
decEq-⊢ (` x) (` x₁) with x ≟ x₁
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (` x) (ƛ t₁) = no (λ ())
decEq-⊢ (` x) (t₁ · t₂) = no (λ ())
decEq-⊢ (` x) (force t₁) = no (λ ())
decEq-⊢ (` x) (delay t₁) = no (λ ())
decEq-⊢ (` x) (con x₁) = no (λ ())
decEq-⊢ (` x) (constr i xs) = no (λ ())
decEq-⊢ (` x) (case t₁ ts) = no (λ ())
decEq-⊢ (` x) (builtin b) = no (λ ())
decEq-⊢ (` x) error = no (λ ())
decEq-⊢ (ƛ t) (` x) = no (λ ())
decEq-⊢ (ƛ t) (ƛ t₁) with t ≟ t₁
... | yes p = yes (cong ƛ p)
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (ƛ t) (t₁ · t₂) = no (λ ())
decEq-⊢ (ƛ t) (force t₁) = no (λ ())
decEq-⊢ (ƛ t) (delay t₁) = no (λ ())
decEq-⊢ (ƛ t) (con x) = no (λ ())
decEq-⊢ (ƛ t) (constr i xs) = no (λ ())
decEq-⊢ (ƛ t) (case t₁ ts) = no (λ ())
decEq-⊢ (ƛ t) (builtin b) = no (λ ())
decEq-⊢ (ƛ t) error = no (λ ())
decEq-⊢ (t · t₂) (` x) = no (λ ())
decEq-⊢ (t · t₂) (ƛ t₁) = no (λ ())
decEq-⊢ (t · t₂) (t₁ · t₃) with (t ≟ t₁) ×-dec (t₂ ≟ t₃)
... | yes ( refl , refl )  = yes refl
... | no ¬p = no λ { refl → ¬p (refl , refl) }
decEq-⊢ (t · t₂) (force t₁) = no (λ ())
decEq-⊢ (t · t₂) (delay t₁) = no (λ ())
decEq-⊢ (t · t₂) (con x) = no (λ ())
decEq-⊢ (t · t₂) (constr i xs) = no (λ ())
decEq-⊢ (t · t₂) (case t₁ ts) = no (λ ())
decEq-⊢ (t · t₂) (builtin b) = no (λ ())
decEq-⊢ (t · t₂) error = no (λ ())
decEq-⊢ (force t) (` x) = no (λ ())
decEq-⊢ (force t) (ƛ t₁) = no (λ ())
decEq-⊢ (force t) (t₁ · t₂) = no (λ ())
decEq-⊢ (force t) (force t₁) with t ≟ t₁
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (force t) (delay t₁) = no (λ ())
decEq-⊢ (force t) (con x) = no (λ ())
decEq-⊢ (force t) (constr i xs) = no (λ ())
decEq-⊢ (force t) (case t₁ ts) = no (λ ())
decEq-⊢ (force t) (builtin b) = no (λ ())
decEq-⊢ (force t) error = no (λ ())
decEq-⊢ (delay t) (` x) = no (λ ())
decEq-⊢ (delay t) (ƛ t₁) = no (λ ())
decEq-⊢ (delay t) (t₁ · t₂) = no (λ ())
decEq-⊢ (delay t) (force t₁) = no (λ ())
decEq-⊢ (delay t) (delay t₁) with t ≟ t₁
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (delay t) (con x) = no (λ ())
decEq-⊢ (delay t) (constr i xs) = no (λ ())
decEq-⊢ (delay t) (case t₁ ts) = no (λ ())
decEq-⊢ (delay t) (builtin b) = no (λ ())
decEq-⊢ (delay t) error = no (λ ())
decEq-⊢ (con x) (` x₁) = no (λ ())
decEq-⊢ (con x) (ƛ t₁) = no (λ ())
decEq-⊢ (con x) (t₁ · t₂) = no (λ ())
decEq-⊢ (con x) (force t₁) = no (λ ())
decEq-⊢ (con x) (delay t₁) = no (λ ())
decEq-⊢ (con x) (con x₁) with x ≟ x₁
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (con x) (constr i xs) = no (λ ())
decEq-⊢ (con x) (case t₁ ts) = no (λ ())
decEq-⊢ (con x) (builtin b) = no (λ ())
decEq-⊢ (con x) error = no (λ ())
decEq-⊢ (constr i xs) (` x) = no (λ ())
decEq-⊢ (constr i xs) (ƛ t₁) = no (λ ())
decEq-⊢ (constr i xs) (t₁ · t₂) = no (λ ())
decEq-⊢ (constr i xs) (force t₁) = no (λ ())
decEq-⊢ (constr i xs) (delay t₁) = no (λ ())
decEq-⊢ (constr i xs) (con x) = no (λ ())
decEq-⊢ (constr i xs) (constr i₁ xs₁) with (i ≟ i₁) ×-dec  (xs ≟ xs₁)
... | yes (refl , refl) = yes refl
... | no ¬pq = no λ { refl → ¬pq (refl , refl) } 
decEq-⊢ (constr i xs) (case t₁ ts) = no (λ ())
decEq-⊢ (constr i xs) (builtin b) = no (λ ())
decEq-⊢ (constr i xs) error = no (λ ())
decEq-⊢ (case t ts) (` x) = no (λ ())
decEq-⊢ (case t ts) (ƛ t₁) = no (λ ())
decEq-⊢ (case t ts) (t₁ · t₂) = no (λ ())
decEq-⊢ (case t ts) (force t₁) = no (λ ())
decEq-⊢ (case t ts) (delay t₁) = no (λ ())
decEq-⊢ (case t ts) (con x) = no (λ ())
decEq-⊢ (case t ts) (constr i xs) = no (λ ())
decEq-⊢ (case t ts) (case t₁ ts₁) with (decEq-⊢ t t₁) ×-dec (ts ≟ ts₁)
... | yes (refl , refl) = yes refl
... | no ¬pq = no λ { refl → ¬pq (refl , refl) } 
decEq-⊢ (case t ts) (builtin b) = no (λ ())
decEq-⊢ (case t ts) error = no (λ ())
decEq-⊢ (builtin b) (` x) = no (λ ())
decEq-⊢ (builtin b) (ƛ t₁) = no (λ ())
decEq-⊢ (builtin b) (t₁ · t₂) = no (λ ())
decEq-⊢ (builtin b) (force t₁) = no (λ ())
decEq-⊢ (builtin b) (delay t₁) = no (λ ())
decEq-⊢ (builtin b) (con x) = no (λ ())
decEq-⊢ (builtin b) (constr i xs) = no (λ ())
decEq-⊢ (builtin b) (case t₁ ts) = no (λ ())
decEq-⊢ (builtin b) (builtin b₁) with b ≟ b₁
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
decEq-⊢ (builtin b) error = no (λ ())
decEq-⊢ error (` x) = no (λ ())
decEq-⊢ error (ƛ t₁) = no (λ ())
decEq-⊢ error (t₁ · t₂) = no (λ ())
decEq-⊢ error (force t₁) = no (λ ())
decEq-⊢ error (delay t₁) = no (λ ())
decEq-⊢ error (con x) = no (λ ())
decEq-⊢ error (constr i xs) = no (λ ())
decEq-⊢ error (case t₁ ts) = no (λ ())
decEq-⊢ error (builtin b) = no (λ ())
decEq-⊢ error error = yes refl

```
