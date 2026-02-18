---
title: VerifiedCompilation.UForceCaseDelay
layout: page
---

# Force-Case-Delay Translation Phase
```
module VerifiedCompilation.UForceCaseDelay where

open import Data.Nat using (ℕ)
open import Untyped 
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; MatchOrCE; forceCaseDelayT)
open import Data.List using (List; _∷_; [])
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped.Equality using (_≟_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong₂; subst; subst₂; cong)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All; all?)

variable
  n : ℕ
  M N : n ⊢
  scrut : n ⊢
  alts : List (n ⊢)

-- force (case scrut [\x1... -> delay term_1, ..., \x1... -> delay term_m])

data IsBranch : n ⊢ → Set where
  B-delay : IsBranch (delay M)
  B-ƛ : IsBranch M → IsBranch (ƛ M)

isBranch? : (t : n ⊢) → Dec (IsBranch t)
isBranch? (delay t) = yes B-delay
isBranch? (ƛ t) with isBranch? t
... | yes p = yes (B-ƛ p)
... | no ¬p = no λ { (B-ƛ x) → ¬p x }
isBranch? (` x) = no λ ()
isBranch? (t · t₁) = no λ ()
isBranch? (force t) = no λ ()
isBranch? (con x) = no λ ()
isBranch? (constr i xs) = no λ ()
isBranch? (case t ts) = no λ ()
isBranch? (builtin b) = no λ ()
isBranch? error = no λ ()

removeDelay : List (n ⊢) → List (n ⊢)
removeDelay l = Data.List.map go l
  where
    go : n ⊢ → n ⊢
    go (delay M) = M
    go (ƛ M) = ƛ (go M)
    go t = t

data FCD : (n ⊢) → (n ⊢) → Set where
  isFCD
    : All IsBranch alts
    → FCD (force (case scrut alts)) (case scrut (removeDelay alts))

isFCD? : MatchOrCE (FCD {n})
isFCD? t t' with (isForce? (isCase? isTerm? allTerms?)) t
... | no ¬matchFst = ce (λ { (isFCD _) → ¬matchFst (isforce (iscase (isterm _) (allterms _))) }) forceCaseDelayT t t'
... | yes (isforce (iscase (isterm scrut) (allterms alts))) with (isCase? isTerm? allTerms?) t'
... | no ¬matchSnd = ce (λ { (isFCD _) → ¬matchSnd (iscase (isterm _) (allterms _)) }) forceCaseDelayT t t'
... | yes (iscase (isterm scrut') (allterms alts')) with scrut ≟ scrut'
... | no ¬scrutEq = ce (λ { (isFCD _) → ¬scrutEq refl }) forceCaseDelayT t t'
... | yes scrutEq with alts' ≟ removeDelay alts
... | no ¬altsEq = ce (λ { (isFCD _) → ¬altsEq refl }) forceCaseDelayT t t'
... | yes altsEq with all? isBranch? alts
... | no ¬allBranch = ce (λ { (isFCD p) → ¬allBranch p }) forceCaseDelayT t t'
... | yes allBranch = proof (subst₂ (λ s a → FCD (force (case scrut alts)) (case s a)) 
                                     scrutEq (sym altsEq) (isFCD allBranch))

ForceCaseDelay : (ast : n ⊢) → (ast' : n ⊢) → Set
ForceCaseDelay = Translation FCD

isForceCaseDelay? : MatchOrCE (ForceCaseDelay {n})
isForceCaseDelay? = translation? forceCaseDelayT isFCD?

fstTest1 : n ⊢
fstTest1 = force (case error (delay error ∷ []))

sndTest1 : n ⊢
sndTest1 = case error (error ∷ [])

fstTest2 : n ⊢
fstTest2 = force (case error (delay error ∷ []))

sndTest2 : n ⊢
sndTest2 = case error ((delay error) ∷ [])

fstTest3 : n ⊢
fstTest3 = case error (ƛ (force (case error (delay error ∷ []))) ∷ [])

sndTest3 : n ⊢
sndTest3 = case error (ƛ (case error (error ∷ [])) ∷ [])

fstTest4 : n ⊢
fstTest4 = case error (ƛ (force (case error (delay fstTest1 ∷ []))) ∷ [])

sndTest4 : n ⊢
sndTest4 = case error (ƛ (case error (fstTest1 ∷ [])) ∷ [])

-- This should fail, but it doesn't because the decision procedure only checks
-- if there is one case of forceCaseDelay, but this has two, and the second is
-- incorrect
fstTest5 : n ⊢
fstTest5 = case error (ƛ (force (case error (delay fstTest2 ∷ []))) ∷ [])

sndTest5 : n ⊢
sndTest5 = case error (ƛ (case error (fstTest2 ∷ [])) ∷ [])


```