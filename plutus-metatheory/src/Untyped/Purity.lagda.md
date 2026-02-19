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
open import Builtin using (Builtin; arity; arity₀)
open import RawU using (TmCon)
open import Data.Product using (_,_; _×_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _>_; _>?_)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just; nothing; from-just)
open import Data.Maybe.Properties using (just-injective)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality.Core using (trans; _≢_; subst; sym; cong)
open import Data.Empty using (⊥)
open import Function.Base using (case_of_)
open import Untyped.CEK using (lookup?)
open import VerifiedCompilation.UntypedViews using (isDelay?; isTerm?; isLambda?; isdelay; isterm; islambda)
open import Untyped.Reduction using (iterApp; Arity; want; no-builtin; sat)
```
## Saturation

The `sat` function is used to measure whether a builtin at the bottom of a
sub-tree of `force` and applications is now saturated and ready to reduce.

```
data Pure {X : ℕ} : (X ⊢) → Set where
    force : {t : X ⊢} → Pure t → Pure (force (delay t))

    constr : {i : ℕ} {xs : List (X ⊢)} → All Pure xs → Pure (constr i xs)

    -- This assumes there are no builtins with arity 0
    -- Or, if there are, they can just be replaced by a
    -- constant before this stage!
    builtin : {b : Builtin} → Pure (builtin b)

    -- To be pure, a term needs to be still unsaturated
    -- after it has been force'd or had something applied
    -- hence, unsat-builtin₀ and unsat-builtin₁ have
    -- (suc (suc _)) requirements.
    unsat-builtin₀ : {t : X ⊢} {a₀ a₁ : ℕ}
            → sat t ≡ want (suc (suc a₀)) a₁
            → Pure t
            → Pure (force t)

    -- unsat-builtin₀₋₁ handles the case where
    -- we consume the last type argument but
    -- still have some unsaturated term args.
    unsat-builtin₀₋₁ : {t : X ⊢} {a₁ : ℕ}
            → sat t ≡ want (suc zero) (suc a₁)
            → Pure t
            → Pure (force t)

    unsat-builtin₁ : {t t₁ : X ⊢} {a₁ : ℕ}
            → sat t ≡ want zero (suc (suc a₁))
            → Pure t
            → Pure t₁
            → Pure (t · t₁)

    -- This is deliberately not able to cover all applications
    -- ƛ (error) · t -- not pure
    -- ƛ ƛ (error) · t · n -- not pure
    -- ƛ ƛ ( (` nothing) · (` just nothing) ) · (ƛ error) · t -- not pure
    -- Double application is considered impure (Unknown) by
    -- the Haskell implementation at the moment.
    app : {l : suc X ⊢} {r : X ⊢}
            → Pure l
            → Pure r
            → Pure ((ƛ l) · r)

    var : {v : Fin X} → Pure (` v)
    delay : {t : X ⊢} → Pure (delay t)
    ƛ : {t : (suc X) ⊢} → Pure (ƛ t)
    con : {c : TmCon} → Pure (con c)
    -- all `case` and `error` terms are considered impure.

isPure? : {X : ℕ} → (t : X ⊢) → Dec (Pure t)

allPure? : {X : ℕ} → (ts : List (X ⊢)) → Dec (All Pure ts)
allPure? [] = yes All.[]
allPure? (t ∷ ts) with (isPure? t) ×-dec (allPure? ts)
... | yes (p , ps) = yes (p All.∷ ps)
... | no ¬p = no λ { (px All.∷ x) → ¬p (px , x) }

isPure? (` x) = yes var
isPure? (ƛ t) = yes ƛ
isPure? (l · r) with isLambda? (isTerm?) l
... | yes (islambda (isterm l₁)) with (isPure? l₁) ×-dec (isPure? r)
...   | yes (pl , pr) = yes (app pl pr)
...   | no ¬pl-pr = no λ { (app pl pr) → ¬pl-pr (pl , pr) }
isPure? (l · r) | no ¬lambda with sat l in sat-l
... | no-builtin = no (λ { (unsat-builtin₁ sat-l₁ pl pr) → contradiction (trans (sym sat-l) sat-l₁) (λ ()) ; (app xx xx₁) → ¬lambda (islambda (isterm _)) })
... | want zero zero = no (λ { (unsat-builtin₁ sat-l₁ xx xx₁) → contradiction ((trans (sym sat-l) sat-l₁)) (λ ()) })
... | want zero (suc zero) = no (λ { (unsat-builtin₁ sat-l₁ xx xx₁) → contradiction ((trans (sym sat-l) sat-l₁)) (λ ()) })
... | want (suc x) x₁ = no (λ { (unsat-builtin₁ sat-l₁ xx xx₁) → contradiction ((trans (sym sat-l) sat-l₁)) (λ ()) })
... | want zero (suc (suc a₁)) with (isPure? l) ×-dec (isPure? r)
...   | yes (pl , pr) = yes (unsat-builtin₁ sat-l pl pr)
...   | no ¬pl-pr = no (λ { (unsat-builtin₁ x xx xx₁) → ¬pl-pr (xx , xx₁) })
isPure? (force t) with isDelay? (isTerm?) t
... | no ¬delay with sat t in sat-t
...   | no-builtin = no (λ {
                     (force xx) → ¬delay (isdelay (isterm _)) ;
                     (unsat-builtin₀ sat-t₁ pt) → contradiction (trans (sym sat-t) sat-t₁) λ ();
                     (unsat-builtin₀₋₁ sat-t₁ pt) → contradiction (trans (sym sat-t) sat-t₁) λ ()
                     })
...   | want zero x₁ = no λ {
                     (unsat-builtin₀ sat-t₁ pt) → contradiction (trans (sym sat-t) sat-t₁) (λ ());
                     (unsat-builtin₀₋₁ sat-t₁ pt) → contradiction (trans (sym sat-t) sat-t₁) λ ()
                     }
... | want (suc zero) zero = no λ {
                     (unsat-builtin₀ sat-t₁ pt) → contradiction (trans (sym sat-t) sat-t₁) (λ ());
                     (unsat-builtin₀₋₁ sat-t₁ pt) → contradiction (trans (sym sat-t) sat-t₁) λ ()
                     }
... | want (suc zero) (suc x₁) with isPure? t
...    | no ¬pt = no λ { (unsat-builtin₀ x xx) → ¬pt xx ; (unsat-builtin₀₋₁ x xx) → ¬pt xx }
...    | yes pt = yes (unsat-builtin₀₋₁ sat-t pt)
isPure? (force t) | no ¬delay | want (suc (suc x)) x₁ with isPure? t
...     | no ¬pt = no λ {(unsat-builtin₀ x pt) → ¬pt pt; (unsat-builtin₀₋₁ x xx) → ¬pt xx}
...     | yes pt = yes (unsat-builtin₀ sat-t pt)
isPure? (force t) | yes (isdelay (isterm tt)) with isPure? tt
...    | yes p = yes (force p)
...    | no ¬p = no λ { (force x) → ¬p x }
isPure? (delay t) = yes delay
isPure? (con x) = yes con
isPure? (constr i xs) with allPure? xs
... | yes pp = yes (constr pp)
... | no ¬pp = no λ { (constr x) → ¬pp x }
isPure? (case scrut ts) =  no λ ()
isPure? (builtin b) = yes builtin
isPure? error = no λ ()
```
