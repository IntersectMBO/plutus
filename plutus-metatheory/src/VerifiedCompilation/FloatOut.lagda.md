---
title: VerifiedCompilation.FloatOut
layout: page
---

# Let Float Out
```
module VerifiedCompilation.FloatOut where

open import Function using (case_of_)
open import Data.Nat using (suc; zero)
open import Data.List using (List; map)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no; does; _×-dec_)

open import Untyped
open import VerifiedCompilation.UntypedViews
open import Untyped.RenamingSubstitution using (weaken)
open import Untyped.Relation.Binary
open import Untyped.Relation.Binary.Modular

open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; LetFloatOutT; Proof?; abort)
```

## Relation rules

```
data FloatApply (@++ R : Relation) : Relation where
  float-apply :
    ∀ {X} {M N K : X ⊢} {L N' : suc X ⊢}
    → R M (let' K L)
    → R (weaken N) N'
    ----------------------------------------
    → FloatApply R (M · N) (let' K (L · N'))

data FloatCase (@++ R : Relation) : Relation where
  float-case :
    ∀ {X} {M N : X ⊢} {L : suc X ⊢} {Ms Ms'}
    → R M (let' N L)
    → Pointwise R (map weaken Ms) Ms'
    -----------------------------------------------
    → FloatCase R (case M Ms) (let' N (case L Ms'))

data FloatForce (@++ R : Relation) : Relation where
  float-force :
    ∀ {X} {M N : X ⊢} {L : suc X ⊢}
    → R M (let' N L)
    -------------------------------------------
    → FloatForce R (force M) (let' N (force L))
```
## Full relation

Closed under term-compatibility.

```
infix 5 FloatOut
FloatOut : Relation
FloatOut = Fix (CompatTerm + FloatApply + FloatCase + FloatForce)
```

## Decision procedure

```
apply-dec : DecidableT FloatApply
apply-dec R? x y
  with (⋯ ·? ⋯) x
    ×-dec (let'? ⋯ (⋯ ·? ⋯)) y
... | no ¬P = no λ {(float-apply _ _) → ¬P inhabitant}
... | yes (match! M ·! match! N , let'! (match! K) (match! L ·! match! N'))
  with R? M (let' K L) ×-dec R? (weaken N) N'
... | no ¬P = no λ {(float-apply RMM' RNN') → ¬P (RMM' , RNN') }
... | yes (RMM' , RNN') = yes (float-apply RMM' RNN')

case-dec : DecidableT FloatCase
case-dec R? x y
  with (case? ⋯ ⋯) x
     ×-dec (let'? ⋯ (case? ⋯ ⋯)) y
... | no ¬P×Q = no λ {(float-case _ _) → ¬P×Q inhabitant}
... | yes ( case! (match! M) (match! Ms)
          , let'! (match! N) (case! (match! L) (match! Ms'))
          )
  with R? M (let' N L)
       ×-dec (pointwise? R? (map weaken Ms) Ms')
... | no ¬P×Q = no λ {(float-case RMM' RMsMs') → ¬P×Q (RMM' , RMsMs')}
... | yes (RMM' , RMsMs') = yes (float-case RMM' RMsMs')

force-dec : DecidableT FloatForce
force-dec R? x y
  with (force? ⋯) x ×-dec (let'? ⋯ (force? ⋯)) y
... | no ¬P×Q = no λ {(float-force _) → ¬P×Q inhabitant}
... | yes (force! (match! M) , let'! (match! M') (force! (match! N')))
  with R? M (let' M' N')
... | no ¬P = no λ {(float-force RMM') → ¬P RMM'}
... | yes RNN' = yes (float-force RNN')
```

When composing the decision procedure, we first check for compatibility rules
and only if that fails do we check for the let-floating rules, because we expect
to more often see a compatibility case:

```
dec : DecidableRel FloatOut
dec = Fix-dec (compatTerm? +-dec apply-dec +-dec case-dec +-dec force-dec)
```

Wrapper for `ProofOrCE`:
```
decide : ∀ {X} (M M' : X ⊢) → ProofOrCE (FloatOut M M')
decide M M' = case dec M M' of λ where
  (yes P) → proof P
  (no ¬P) → ce ¬P LetFloatOutT M M'
  -- note: using a with-abstraction here instead of case_of_ causes agda to hang
  -- possibly due to infinite unfolding of dec?
```

## Example tests

```
private module Examples where
  open import Relation.Binary.PropositionalEquality
  open import Data.Bool
  open import Data.List using ([])
  open import Data.Fin

  c : ∀ {X} → X ⊢
  c = constr 0 []

  id : ∀ {X} → X ⊢
  id = ƛ (` zero)
```

Basic behaviour:

```
  M M' : 1 ⊢
  M  = (let' id c) · c
  M' = let' id (c · c)

  _ : does (dec M M') ≡ true
  _ = refl

  _ : does (dec M' M) ≡ false
  _ = refl

  N N' : 0 ⊢
  N  = force (let' id c)
  N' = let' id (force c )

  _ : does (dec N N') ≡ true
  _ = refl
```

Floating out multiple levels:

```
  L L' : 0 ⊢
  L  = force ( force (let' id c))
  L' = let' (ƛ (` zero)) (force (force (constr 0 [])))

  LL' : does (dec L L') ≡ true
  LL' = refl

  H H' : 0 ⊢
  H  = ((let' id c) · c) · c
  H' = let' id (c · c · c)

  HH' : does (dec H H') ≡ true
  HH' = refl
```

Floating in multiple places

```
  K K' : 0 ⊢
  K = force (let' id M)
  K' = let' id (force M')

  _ : does (dec K K') ≡ true
  _ = refl
```
