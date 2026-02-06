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

`Policy` determines whether the certifier should succeed or fail when certifying
this relation.

```
data Policy : Set where
  accept : Policy
  reject : Policy
```

`NotImplemented reject` is an empty type, whereas `NotImplemented accept` has a
trivial inhabitant.

```
data NotImplemented {X} : Policy → (X ⊢) → (X ⊢) → Set where
  notImplemented : ∀ {M N} → NotImplemented accept M N

certNotImplemented : Certifier (NotImplemented {0} accept)
certNotImplemented _ _ = proof notImplemented
```
