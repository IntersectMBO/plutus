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

record DecEq (A : Set) : Set where
  field _≟_ : DecidableEquality A
open DecEq {{...}} public

postulate
   -- This is fairly straightforward to define but it depends on
   -- DecidableEquality over various Agda builtin types, which is
   -- easy to do but should be in the starndard library *somewhere*??
   decEq-TyCon : {t : TyTag} → DecidableEquality (⟦ t ⟧tag)
   decEq-TmCon : DecidableEquality TmCon
   
{-
  DecEq-TmCon ._≟_ tc1 tc2 with decTagCon (tmCon2TagCon tc1) (tmCon2TagCon tc2)
  ...                                                                            | true           = yes {!!}
  ...                                                                            | false          = no  {!!}
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

