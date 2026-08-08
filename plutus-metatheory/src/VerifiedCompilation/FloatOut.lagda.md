---
title: VerifiedCompilation.FloatOut
layout: page
---

# Let Float Out
```
module VerifiedCompilation.FloatOut where

open import Function using (case_of_)
open import Data.Nat using (suc; zero; ℕ; _+_)
open import Data.List using (List; map)
open import Data.Product using (_,_; ∃)
open import Relation.Nullary using (Dec; yes; no; does; _×-dec_)

open import Untyped
open import VerifiedCompilation.UntypedViews
open import Untyped.RenamingSubstitution using (weaken)
open import Untyped.Relation.Binary
open import Untyped.Relation.Binary.Modular
open import Untyped.Relation.Binary.Modular.Patterns

open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; LetFloatOutT; Proof?; abort)
```

## Relation rules

```
data FloatApply (@++ R : Relation) : Relation where
  float-apply :
    ∀ {n} {M N K : n ⊢} {L N' : suc n ⊢}
    → R M (let₁ K L)
    → R (weaken N) N'
    ----------------------------------------
    → FloatApply R (M · N) (let₁ K (L · N'))

data FloatCase (@++ R : Relation) : Relation where
  float-case :
    ∀ {n} {M N : n ⊢} {L : suc n ⊢} {Ms Ms'}
    → R M (let₁ N L)
    → Pointwise R (map weaken Ms) Ms'
    -----------------------------------------------
    → FloatCase R (case M Ms) (let₁ N (case L Ms'))

data FloatForce (@++ R : Relation) : Relation where
  float-force :
    ∀ {n} {M N : n ⊢} {L : suc n ⊢}
    → R M (let₁ N L)
    -------------------------------------------
    → FloatForce R (force M) (let₁ N (force L))
```
## Full relation

Closed under term-compatibility.

```
infix 5 FloatOut
FloatOut : Relation
FloatOut = Fix (CompatTerm ⊕ FloatApply ⊕ FloatCase ⊕ FloatForce ⊕ Empty)
```

## Decision procedure

```
apply-dec : DecidableT FloatApply
apply-dec R? x y
  with (⋯ ·? ⋯) x
    ×-dec (let₁? ⋯ (⋯ ·? ⋯)) y
... | no ¬P = no λ {(float-apply _ _) → ¬P inhabitant}
... | yes (match! M ·! match! N , let₁! (match! K) (match! L ·! match! N'))
  with R? M (let₁ K L) ×-dec R? (weaken N) N'
... | no ¬P = no λ {(float-apply RMM' RNN') → ¬P (RMM' , RNN') }
... | yes (RMM' , RNN') = yes (float-apply RMM' RNN')

case-dec : DecidableT FloatCase
case-dec R? x y
  with (case? ⋯ ⋯) x
     ×-dec (let₁? ⋯ (case? ⋯ ⋯)) y
... | no ¬P×Q = no λ {(float-case _ _) → ¬P×Q inhabitant}
... | yes ( case! (match! M) (match! Ms)
          , let₁! (match! N) (case! (match! L) (match! Ms'))
          )
  with R? M (let₁ N L)
       ×-dec (pointwise? R? (map weaken Ms) Ms')
... | no ¬P×Q = no λ {(float-case RMM' RMsMs') → ¬P×Q (RMM' , RMsMs')}
... | yes (RMM' , RMsMs') = yes (float-case RMM' RMsMs')

force-dec : DecidableT FloatForce
force-dec R? x y
  with (force? ⋯) x ×-dec (let₁? ⋯ (force? ⋯)) y
... | no ¬P×Q = no λ {(float-force _) → ¬P×Q inhabitant}
... | yes (force! (match! M) , let₁! (match! M') (force! (match! N')))
  with R? M (let₁ M' N')
... | no ¬P = no λ {(float-force RMM') → ¬P RMM'}
... | yes RNN' = yes (float-force RNN')
```

When composing the decision procedure, we first check for compatibility rules
and only if that fails do we check for the let-floating rules, because we expect
to more often see a compatibility case:

```
dec : DecidableRel FloatOut
dec = Fix-dec (compatTerm? ⊕-dec apply-dec ⊕-dec case-dec ⊕-dec force-dec ⊕-dec empty?)
```

Wrapper for `ProofOrCE`:
```
decide : ∀ {n} (M M' : n ⊢) → ProofOrCE (FloatOut M M')
decide M M' = case dec M M' of λ where
  (yes P) → proof P
  (no ¬P) → ce ¬P LetFloatOutT M M'
  -- note: using a with-abstraction here instead of case_of_ causes agda to hang
  -- possibly due to infinite unfolding of dec?
```

## Counting optimization sites

```
numSites : ∀ {n} {M N : n ⊢} → FloatOut M N → ℕ
numSites* : ∀ {n} {Ms Ns : List (n ⊢)} → Pointwise FloatOut Ms Ns → ℕ
numSites-compat : ∀ {n} {M N : n ⊢} → CompatTerm FloatOut M N → ℕ

numSites (fix (inj₀ P)) = numSites-compat P
numSites (fix (inj₁ (float-apply RM RN))) = 1 + numSites RM + numSites RN
numSites (fix (inj₂ (float-case RM RMs))) = 1 + numSites RM + numSites* RMs
numSites (fix (inj₃ (float-force RM))) = 1 + numSites RM

numSites* [] = 0
numSites* (RM ∷ RMs) = numSites RM + numSites* RMs

numSites-compat compat-conF = 0
numSites-compat compat-builtinF = 0
numSites-compat compat-errorF = 0
numSites-compat (compat-varF _) = 0
numSites-compat (compat-lambdaF P) = numSites P
numSites-compat (compat-applyF P Q) = numSites P + numSites Q
numSites-compat (compat-forceF P) = numSites P
numSites-compat (compat-delayF P) = numSites P
numSites-compat (compat-constrF Ps) = numSites* Ps
numSites-compat (compat-caseF P Ps) = numSites P + numSites* Ps
```

## Example tests

```
private module Examples where
  open import Relation.Binary.PropositionalEquality
  open import Data.Bool
  open import Data.List using ([])
  open import Data.Fin

  c : ∀ {n} → n ⊢
  c = constr 0 []

  id : ∀ {n} → n ⊢
  id = ƛ (` zero)
```

Basic behaviour:

```
  M M' : 1 ⊢
  M  = (let₁ id c) · c
  M' = let₁ id (c · c)

  _ : does (dec M M') ≡ true
  _ = refl

  _ : does (dec M' M) ≡ false
  _ = refl

  N N' : 0 ⊢
  N  = force (let₁ id c)
  N' = let₁ id (force c )

  _ : does (dec N N') ≡ true
  _ = refl
```

Floating out multiple levels:

```
  L L' : 0 ⊢
  L  = force ( force (let₁ id c))
  L' = let₁ (ƛ (` zero)) (force (force (constr 0 [])))

  LL' : does (dec L L') ≡ true
  LL' = refl

  H H' : 0 ⊢
  H  = ((let₁ id c) · c) · c
  H' = let₁ id (c · c · c)

  HH' : does (dec H H') ≡ true
  HH' = refl
```

Floating in multiple places

```
  K K' : 0 ⊢
  K = force (let₁ id M)
  K' = let₁ id (force M')

  _ : does (dec K K') ≡ true
  _ = refl
```
