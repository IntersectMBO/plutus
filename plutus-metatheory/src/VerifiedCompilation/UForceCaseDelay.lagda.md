---
title: VerifiedCompilation.UForceCaseDelay
layout: page
---

# Force-Case-Delay Translation Phase
```
module VerifiedCompilation.UForceCaseDelay where

open import Data.Nat using (ℕ)
open import Untyped using (_⊢)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; MatchOrCE; forceCaseDelayT)

variable
  X : ℕ
  x x' y y' : X ⊢

data FCD : (X ⊢) → (X ⊢) → Set where
  fcd : FCD x x'

isFCD? : MatchOrCE (FCD {X})
isFCD? = λ a b → proof fcd

ForceCaseDelay : (ast : X ⊢) → (ast' : X ⊢) → Set
ForceCaseDelay = Translation FCD

isForceCaseDelay? : MatchOrCE (ForceCaseDelay {X})
isForceCaseDelay? = translation? forceCaseDelayT isFCD?

```