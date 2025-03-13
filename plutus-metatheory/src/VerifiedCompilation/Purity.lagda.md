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
open import Builtin using (Builtin; arity)
open import Utils as U using (Maybe;nothing;just)
open import RawU using (TmCon)
open import Data.Product using (_,_; _×_)
open import Data.Nat using (ℕ; zero; suc; _>_; _>?_)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing; Is-nothing)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality.Core using (trans; _≢_; subst; sym)
```
## Untyped Purity

The definition here is based on the (Haskell Implementation)[https://github.com/IntersectMBO/plutus/blob/master/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Purity.hs]. It is mostly uncontentious.
```
-- FIXME: The  problem with this is that `builtin b` is unsaturated because it
-- is (arity , zero), and so it is Pure, and so everthing recursive will just treat it
-- as Pure and not bother thinking harder...
saturation : {X : Set} → X ⊢ → Maybe (ℕ × ℕ)
saturation (builtin b) = just (((arity b), zero))
saturation (t · _) with saturation t
... | nothing = nothing
... | just (arity , apps) = just (arity , suc apps)
saturation (force t) with saturation t
... | nothing = nothing
... | just (arity , apps) = just (arity , suc apps)
saturation _ = nothing


data Pure {X : Set} : (X ⊢) → Set where
    force : {t : X ⊢} → Pure t → Pure (force t)

    constr : {i : ℕ} {xs : List (X ⊢)} → All Pure xs → Pure (constr i xs)
    case : {t : X ⊢} {ts : List (X ⊢)} → Pure t → All Pure ts → Pure (case t ts)

    builtin : {b : Builtin} → Pure (builtin b)

    unsat-builtin : {t₁ t₂ : X ⊢} {arity args : ℕ}
            → saturation t₁ ≡ just (arity , args)
            → arity > (suc args)
            → Pure (t₁ · t₂)
    app : {l r : X ⊢}
            → saturation l ≡ nothing -- This doesn't have a builtin at the bottom.
            → Pure l
            → Pure r
            → Pure (l · r)

    var : {v : X} → Pure (` v)
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
isPure? (l · r) with saturation l in sat-l
isPure? (l · r) | nothing with (isPure? l) ×-dec (isPure? r)
isPure? (l · r) | nothing | yes (pl , pr) = yes (app sat-l pl pr)
isPure? (l · r) | nothing | no ¬p = no λ {
                              (unsat-builtin sat-l=just _) → {!!}
                            ; (app x x₁ x₂) → ¬p (x₁ , x₂)
                            }
isPure? (l · r) | just (arity , args) with arity >? (suc args)
... | yes arity<args = yes (unsat-builtin sat-l  arity<args)
... | no ¬arity<args = no λ {
                          (unsat-builtin sat-l=just arity<args) → contradiction arity<args {!!}
                          ; (app x x₁ x₂) → {!!}
                          }
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
