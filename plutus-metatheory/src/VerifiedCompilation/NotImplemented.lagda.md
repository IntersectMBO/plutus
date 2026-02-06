---
title: NotImplemented
layout: page
---

A placeholder relation for unspecified compiler passes.

```
module VerifiedCompilation.NotImplemented where

open import Untyped
open import VerifiedCompilation.Certificate
import Data.Nat using (ℕ)
```

Depending on whether the certifier should fail or 
The `NotImplemented true` is trivially inhabited, while `NotImplemented false` is empty.

```
data Policy : Set where
  accept : Policy
  reject : Policy

data NotImplemented {X} : Policy → (X ⊢) → (X ⊢) → Set where
  notImplemented : ∀ {M N} → NotImplemented accept M N

certNotImplemented : Certifier (NotImplemented {0} accept)
certNotImplemented _ _ = proof notImplemented
```
