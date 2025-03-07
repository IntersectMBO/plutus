---
title: VerifiedCompilation.Purity
layout: page
---

# Definitions of Purity for Terms
```
module VerifiedCompilation.Purity where

```
## Imports

```
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
open import Builtin using (Builtin)
open import Utils as U using (Maybe;nothing;just)
open import RawU using (TmCon)
open import Data.Product using (_,_)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All)
```
## Untyped Purity

The definition here is based on the (Haskell Implementation)[https://github.com/IntersectMBO/plutus/blob/master/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Purity.hs]. It is mostly uncontentious.
```
data Pure {X : Set} : (X ⊢) → Set where
    app : {l r : X ⊢} → Pure l → Pure r → Pure (l · r)
    force : {t : X ⊢} → Pure t → Pure (force t)

    constr : {i : ℕ} {xs : List (X ⊢)} → All Pure xs → Pure (constr i xs)
    case : {t : X ⊢} {ts : List (X ⊢)} → Pure t → All Pure ts → Pure (case t ts)

    var : {v : X} → Pure (` v)
    builtin : {b : Builtin} → Pure (builtin b)
    delay : {t : X ⊢} → Pure (delay t)
    ƛ : {t : (Maybe X) ⊢} → Pure (ƛ t)
    con : {c : TmCon} → Pure (con c)
    -- errors are not pure ever.

isPure? : {X : Set} → (t : X ⊢) → Dec (Pure t)

allPure? : {X : Set} → (ts : List (X ⊢)) → Dec (All Pure ts)
allPure? [] = yes All.[]
allPure? (t ∷ ts) with (isPure? t) ×-dec (allPure? ts)
... | yes (p , ps) = yes (p All.∷ ps)
... | no ¬p = no λ { (px All.∷ x) → ¬p (px , x) }

isPure? (` x) = yes var
isPure? (ƛ t) = yes ƛ
isPure? (l · r) with (isPure? l) ×-dec (isPure? r)
... | yes (pl , pr) = yes (app pl pr)
... | no ¬p = no λ { (app x x₁) → ¬p (x , x₁) }
isPure? (force t) with isPure? t
... | yes p = yes (force p)
... | no ¬p = no λ { (force x) → ¬p x }
isPure? (delay t) = yes delay
isPure? (con x) = yes con
isPure? (constr i xs) with allPure? xs
... | yes pp = yes (constr pp)
... | no ¬pp = no λ { (constr x) → ¬pp x }
isPure? (case t ts) with (isPure? t) ×-dec (allPure? ts)
... | yes (p , ps) = yes (case p ps)
... | no ¬p = no λ { (case x x₁) → ¬p (x , x₁) }
isPure? (builtin b) = yes builtin
isPure? error = no λ ()
```
