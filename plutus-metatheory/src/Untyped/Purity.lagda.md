---
title: VerifiedCompilation.Purity
layout: page
---

# Definitions of Purity for Terms
```
module Untyped.Purity where

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
open import Data.Maybe using (Maybe; just; nothing; from-just)
open import Data.Maybe.Properties using (just-injective)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality.Core using (trans; _≢_; subst; sym; cong)
open import Data.Empty using (⊥)
open import Function.Base using (case_of_)
open import Untyped.CEK using (lookup?)
open import VerifiedCompilation.UntypedViews using (isDelay?; isTerm?; isdelay; isterm)
-- FIXME: This moves to Untyped.Reduction in a different PR...
open import VerifiedCompilation.UCaseReduce using (iterApp)
```
## Untyped Purity

The definition here is based on the (Haskell Implementation)[https://github.com/IntersectMBO/plutus/blob/master/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Purity.hs]. It is mostly uncontentious.
```
saturation : {X : Set} → X ⊢ → Maybe (ℕ × ℕ)
saturation (builtin b) = just (((arity b), zero))
saturation (t · _) with saturation t
... | nothing = nothing
... | just (arity , apps) = just (arity , suc apps)
saturation (force t) with saturation t
... | nothing = nothing
... | just (arity , apps) = just (arity , suc apps)
saturation _ = nothing

sat-det : {X : Set} {arity args arity₁ args₁ : ℕ} {t t₁ : X ⊢}
        → saturation t ≡ just (arity , args)
        → saturation t₁ ≡ just (arity₁ , args₁)
        → t ≡ t₁
        → just (arity , args) ≡ just (arity₁ , args₁)
sat-det sat-t sat-t₁ refl = trans (sym sat-t) sat-t₁

data Pure {X : Set} : (X ⊢) → Set where
    force : {t : X ⊢} → Pure t → Pure (force (delay t))

    constr : {i : ℕ} {xs : List (X ⊢)} → All Pure xs → Pure (constr i xs)
    -- case applied to constr would reduce, and possibly be pure.
    case : {i : ℕ} {t : X ⊢}{vs ts : List (X ⊢)}
           → lookup? i ts ≡ just t
           → Pure (iterApp t vs)
           → Pure (case (constr i vs) ts)
    -- case applied to anything else is Unknown

    builtin : {b : Builtin} → Pure (builtin b)

    unsat-builtin : {t₁ t₂ : X ⊢} {arity args : ℕ}
            → saturation t₁ ≡ just (arity , args)
            → arity > (suc args)
            → Pure t₂
            → Pure (t₁ · t₂)

    -- This is deliberately not able to cover all applications
    -- ƛ (error) · t -- not pure
    -- ƛ ƛ (error) · t · n -- not pure
    -- ƛ ƛ ( (` nothing) · (` just nothing) ) · (ƛ error) · t -- not pure
    -- Double application is considered impure (Unknown) by
    -- the Haskell implementation at the moment.
    app : {l : Maybe X ⊢} {r : X ⊢}
            → Pure l
            → Pure r
            → Pure ((ƛ l) · r)

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

{-# TERMINATING #-}
isPure? (` x) = yes var
isPure? (ƛ t) = yes ƛ
isPure? (l · r) with saturation l in sat-l
isPure? (l · r) | just (arity , args) with arity >? (suc args)
... | no ¬arity>args = no λ { (unsat-builtin sat-l₁ arity>args pr) → contradiction (subst (λ { (ar , ag) → ar > (suc ag) }) (just-injective (trans (sym sat-l₁) sat-l)) arity>args) ¬arity>args }
... | yes arity<args with isPure? r
...   | yes pr = yes (unsat-builtin sat-l arity<args pr)
...   | no ¬pr = no λ { (unsat-builtin _ _ pr) → ¬pr pr ; (app _ pr) → ¬pr pr }
isPure? (` x · r) | nothing = no λ { (unsat-builtin sat-l≡just _ _) → contradiction (trans (sym sat-l) sat-l≡just) (λ ()) }
isPure? (ƛ l · r) | nothing with (isPure? l) ×-dec (isPure? r)
... | yes (pl , pr) = yes (app pl pr)
... | no ¬pl-pr = no λ { (app pl pr) → ¬pl-pr (pl , pr) }
isPure? ((l · l₁) · r) | nothing = no λ { (unsat-builtin sat-l≡just _ _) → contradiction (trans (sym sat-l) sat-l≡just) (λ ()) }
isPure? (force l · r) | nothing = no λ { (unsat-builtin sat-l≡just _ _) → contradiction (trans (sym sat-l) sat-l≡just) (λ ()) }
isPure? (delay l · r) | nothing = no λ { (unsat-builtin sat-l≡just _ _) → contradiction (trans (sym sat-l) sat-l≡just) (λ ()) }
isPure? (con x · r) | nothing = no λ { (unsat-builtin sat-l≡just _ _) → contradiction (trans (sym sat-l) sat-l≡just) (λ ()) }
isPure? (constr i xs · r) | nothing = no λ { (unsat-builtin sat-l≡just _ _) → contradiction (trans (sym sat-l) sat-l≡just) (λ ()) }
isPure? (case l ts · r) | nothing = no λ { (unsat-builtin sat-l≡just _ _) → contradiction (trans (sym sat-l) sat-l≡just) (λ ()) }
isPure? (error · r) | nothing = no λ { (unsat-builtin sat-l≡just _ _) → contradiction (trans (sym sat-l) sat-l≡just) (λ ()) }
isPure? (force t) with isDelay? (isTerm?) t
... | no ¬delay = no λ { (force x) → ¬delay (isdelay (isterm _))}
... | yes (isdelay (isterm tt)) with isPure? tt
...    | yes p = yes (force p)
...    | no ¬p = no λ { (force x) → ¬p x }
isPure? (delay t) = yes delay
isPure? (con x) = yes con
isPure? (constr i xs) with allPure? xs
... | yes pp = yes (constr pp)
... | no ¬pp = no λ { (constr x) → ¬pp x }
isPure? (case (` x) ts) = no (λ ())
isPure? (case (ƛ t) ts) = no (λ ())
isPure? (case (t · t₁) ts) = no (λ ())
isPure? (case (force t) ts) = no (λ ())
isPure? (case (delay t) ts) = no (λ ())
isPure? (case (con x) ts) = no (λ ())
isPure? (case (constr i vs) ts) with lookup? i ts in lookup-i
... | nothing = no λ { (case lookup≡just pt·vs) → contradiction (trans (sym lookup-i) lookup≡just) λ () }
... | just t with isPure? (iterApp t vs)
...   | yes pt·vs = yes (case lookup-i pt·vs)
...   | no ¬p = no λ { (case lookup≡just pt·vs) → contradiction (subst (λ x → Pure (iterApp x vs)) (just-injective (trans (sym lookup≡just) lookup-i)) pt·vs) ¬p }
isPure? (case (case t ts₁) ts) = no (λ ())
isPure? (case (builtin b) ts) = no (λ ())
isPure? (case error ts) = no (λ ())
isPure? (builtin b) = yes builtin
isPure? error = no λ ()
```
