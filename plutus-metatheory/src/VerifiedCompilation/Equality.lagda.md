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
record DecEq (A : Set) : Set where
  field _≟_ : DecidableEquality A
open DecEq {{...}} public
open import Untyped using (_⊢; `; ƛ; case; constr; _·_; force; delay; con; builtin; error)
import Relation.Unary as Unary using (Decidable)
import Relation.Binary.Definitions as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Utils as U using (Maybe; nothing; just; Either)

postulate
   -- This is fairly straightforward to define but it depends on
   -- DecidableEquality over various Agda builtin types, which is
   -- easy to do but should be in the standard library *somewhere*??
   dec-⟦_⟧tag : ( t : TyTag ) → DecidableEquality ⟦ t ⟧tag
   decEq-⊢ : ∀{X} {{_ : DecEq X}} → DecidableEquality (X ⊢)
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

  DecEq-List⊢ : ∀{X} {{_ : DecEq X}} → DecEq (List (X ⊢))
  DecEq-List⊢ ._≟_ xs ys with decPointwise decEq-⊢ xs ys
  ...                           | yes pw = yes (Pointwise-≡⇒≡ pw)
  ...                           | no ¬pw = no λ x → ¬pw (≡⇒Pointwise-≡ x)

  DecEq-Builtin : DecEq Builtin
  DecEq-Builtin ._≟_ = decBuiltin

  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ ._≟_ = Data.Nat.Properties._≟_

```
