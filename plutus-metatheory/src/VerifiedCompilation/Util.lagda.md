---
title: VerifiedCompilation.Util
layout: page
---
# Verified Compilation General Definitions
```
module VerifiedCompilation.Util where
```

## Decidable Equivalence

We need to determine if two terms refer to the same variable, so we need decidable
equivalence on variables, which are really de Brujin numbers encoded using Maybe.

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; isEquivalence; cong)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Utils as U using (Maybe; nothing; just; Either)
open import RawU using (TmCon; tmCon; decTag; TyTag; ⟦_⟧tag; decTagCon; tmCon2TagCon)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Builtin.Constant.AtomicType using (AtomicTyCon; decAtomicTyCon; ⟦_⟧at)
open import Agda.Builtin.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.Definitions using (Decidable)
open import Level using (Level)
open import Builtin.Signature using (_⊢♯)

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
   

instance
  DecEq-Maybe : ∀{A} {{_ : DecEq A}} → DecEq (Maybe A)
  DecEq-Maybe ._≟_ = M.≡-dec _≟_
    where import Data.Maybe.Properties as M

  DecAtomicTyCon : DecEq AtomicTyCon
  DecAtomicTyCon ._≟_ = decAtomicTyCon

  DecEq-TmCon : DecEq TmCon
  DecEq-TmCon ._≟_ = decEq-TmCon
```

# Pointwise Decisions

At some points we will want to show that one list of AST elements is a valid translation
of another list of AST elements by showing the `n`th element of one is a translation of the
`n`th element of the other, pointwise. 

```
-- postulate
decPointwise : { A B : Set} { _~_ : A → B → Set } → Decidable _~_ → Decidable (Pointwise _~_)
decPointwise dec [] [] = yes Pointwise.[]
decPointwise dec [] (x ∷ ys) = no (λ ())
decPointwise dec (x ∷ xs) [] = no (λ ())
decPointwise dec (x ∷ xs) (y ∷ ys) with dec x y | decPointwise dec xs ys
... | yes p | yes q = yes (p Pointwise.∷ q) 
... | yes _ | no ¬q = no λ where (_ Pointwise.∷ xs~ys) → ¬q xs~ys
... | no ¬p | _     = no λ where (x∼y Pointwise.∷ _) → ¬p x∼y
```

