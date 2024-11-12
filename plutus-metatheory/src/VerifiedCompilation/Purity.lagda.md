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
open import Relation.Nullary using (Dec; yes; no; ¬_)

```
## Untyped Purity
```
data UPure (X : Set) : (X ⊢) → Set where
  FIXME : (t : X ⊢) → UPure X t

isUPure? : {X : Set} → (t : X ⊢) → Dec (UPure X t)
isUPure? t = yes (FIXME t)
```
