---
title: VerifiedCompilation.UForceCaseDelay
layout: page
---

# Force-Case-Delay Translation Phase

```
module VerifiedCompilation.UForceCaseDelay where

```

## Imports

```

open import Data.Nat using (ℕ)
open import Untyped 
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; DecidableCE; forceCaseDelayT; isProof?; isCE?)
open import Data.List using (List; _∷_; [])
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped.Equality using (_≟_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong₂; subst; subst₂; cong)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All; all?)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Data.Bool.Base using (Bool; false; true)

```

## Translation Relation

The Force-Case-Delay compiler optimization phase transforms terms of the form: `force (case scrut [\x1... -> delay term_1, ..., \x1... -> delay term_m])` into `case scrut [\x1... -> term_1, ..., \x1... -> term_m]`. Note that the delay must appear in all the branches of the case, under any number (including zero) of lambda abstractions.

An important remark is that this transformation is not semantics-preserving in general, but it is semantics preserving when the program is "well-formed". We do not have a formal definition of well-formedness, this is left as future work. For more information about the intuitive notion of well-formedness, see `Note [Applying force to delays in case branches]` in the Untyped Plutus Core implementation of the Force-Case-Delay optimization phase.

However, since translation relations are purely syntactic, we do not need to worry about well-formedness in the definition of the translation relation, it will be required only in the proof of semantic preservation, which is left as future work.

In this module, we define the translation relation for the Force-Case-Delay optimization phase.

### Global variable declarations

```

variable
  n : ℕ
  M N : n ⊢
  scrut scrut' : n ⊢
  alts alts' : List (n ⊢)

```

### The `IsBranch` predicate

Two terms are only in the translation relation if the first term's branches are all of the form `delay M` for some `M`, possibly under some number of lambda abstractions. The `IsBranch` predicate captures this condition. The `isBranch?` function is a decision procedure which proves whether a term satisfies the `IsBranch` predicate.

We also define a helper function `removeDelay` which removes the `delay` constructor from the branches, so that we can relate the branches of the first term to the branches of the second term in the definition of the translation relation.

```

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

```

### The definition of the Force-Case-Delay translation relation

Two terms are in the Force-Case-Delay relation (named below `FCD`) if all the branches of the first term satisfy the `IsBranch` predicate, if the second term is obtained from the first by removing the `force` at the top and the `delay` in the branches, and by applying the translation relation recursively to the scrutinee and the branches.

The decision procedure `isForceCaseDelay?` proves that two terms are in the relation and it is the main result of this module. Unfortunately, the terminating pragma is necessary since it is difficult to convince Agda that the recursive calls are on structurally smaller terms.

```

data FCD : (n ⊢) → (n ⊢) → Set where
  isFCD
    : All IsBranch alts
    → Translation FCD scrut scrut'
    → Pointwise (Translation FCD) (removeDelay alts) alts'
    → FCD (force (case scrut alts)) (case scrut' alts')

ForceCaseDelay : (ast : n ⊢) → (ast' : n ⊢) → Set
ForceCaseDelay = Translation FCD

isForceCaseDelay? : DecidableCE (ForceCaseDelay {n})

{-# TERMINATING #-}
isFCD? : DecidableCE (FCD {n})
isFCD? t t' with isForce? (isCase? isTerm? allTerms?) t 
... | no ¬matchLHS = ce (λ { (isFCD p1 p2 p3) → ¬matchLHS (isforce (iscase (isterm _) (allterms _))) } ) forceCaseDelayT t t'
... | yes (isforce (iscase (isterm scrut) (allterms alts))) with isCase? isTerm? allTerms? t'
... | no ¬matchRHS = ce (λ { (isFCD p1 p2 p3) → ¬matchRHS (iscase (isterm _) (allterms _)) } ) forceCaseDelayT t t'
... | yes (iscase (isterm scrut') (allterms alts')) with all? isBranch? alts
... | no ¬areBranches = ce (λ { (isFCD p1 p2 p3) → ¬areBranches p1 } ) forceCaseDelayT t t'
... | yes areBranches with isForceCaseDelay? scrut scrut'
... | ce ¬fcdScrut tag lhs rhs = ce (λ { (isFCD p1 p2 p3) → ¬fcdScrut p2 } ) forceCaseDelayT t t'
... | proof fcdScrut with pcePointwise forceCaseDelayT isForceCaseDelay? (removeDelay alts) alts'
... | ce ¬fcdAlts tag lhs rhs = ce (λ { (isFCD p1 p2 p3) → ¬fcdAlts p3 } ) forceCaseDelayT t t'
... | proof fcdAlts = proof (isFCD areBranches fcdScrut fcdAlts)

isForceCaseDelay? = translation? forceCaseDelayT isFCD?

```

### Test cases

In the following section we present a number of unit tests for the `isForceCaseDelay?` function. These tests are not meant to be exhaustive, but they cover some of the most common edge cases.

```

-- Without lambda abstractions, expected to pass
fstTest1 : n ⊢
fstTest1 = force (case error (delay error ∷ []))

sndTest1 : n ⊢
sndTest1 = case error (error ∷ [])

test1 : isProof? (isForceCaseDelay? {0} fstTest1 sndTest1) ≡ true
test1 = refl


-- Without lambda abstractions, expected to fail because the second term still contains the delay
fstTest2 : n ⊢
fstTest2 = force (case error (delay error ∷ []))

sndTest2 : n ⊢
sndTest2 = case error ((delay error) ∷ [])

test2 : isCE? (isForceCaseDelay? {0} fstTest2 sndTest2) ≡ true
test2 = refl


-- With lambda abstractions, expected to pass
fstTest3 : n ⊢
fstTest3 = case error (ƛ (force (case error (delay error ∷ []))) ∷ [])

sndTest3 : n ⊢
sndTest3 = case error (ƛ (case error (error ∷ [])) ∷ [])

test3 : isProof? (isForceCaseDelay? {0} fstTest3 sndTest3) ≡ true
test3 = refl


-- With lambda abstractions, expected to fail because the second term still contains the delay
fstTest4 : n ⊢
fstTest4 = case error (ƛ (force (case error (delay error ∷ []))) ∷ [])

sndTest4 : n ⊢
sndTest4 = case error (ƛ (case error (delay error ∷ [])) ∷ [])

test4 : isCE? (isForceCaseDelay? {0} fstTest4 sndTest4) ≡ true
test4 = refl


-- Requires traversing the term before reaching the force-case-delay pattern, expected to pass
fstTest5 : n ⊢
fstTest5 = case error (ƛ (force (case error (delay fstTest1 ∷ []))) ∷ [])

sndTest5 : n ⊢
sndTest5 = case error (ƛ (case error (sndTest1 ∷ [])) ∷ [])

test5 : isProof? (isForceCaseDelay? {0} fstTest5 sndTest5) ≡ true
test5 = refl


-- Requires traversing the term before reaching the force-case-delay pattern, and has to
-- check the translation relation recursively, expected to pass
fstTest6 : n ⊢
fstTest6 = force (case error (ƛ (delay (force (case error (delay fstTest1 ∷ [])))) ∷ []))

sndTest6 : n ⊢
sndTest6 = case error (ƛ (case error (sndTest1 ∷ [])) ∷ [])

test6 : isProof? (isForceCaseDelay? {0} fstTest6 sndTest6) ≡ true
test6 = refl


-- Requires traversing the term before reaching the force-case-delay pattern, and has to
-- check the translation relation recursively, expected to fail because the second term
-- still contains the delay, see 'test2'
fstTest7 : n ⊢
fstTest7 = force (case error (ƛ (delay (force (case error (delay fstTest2 ∷ [])))) ∷ []))

sndTest7 : n ⊢
sndTest7 = case error (ƛ (case error (sndTest2 ∷ [])) ∷ [])

test7 : isCE? (isForceCaseDelay? {0} fstTest7 sndTest7) ≡ true
test7 = refl

```