---
title: Untyped.Relation.Binary.Modular.Patterns
layout: page
---

```
module Untyped.Relation.Binary.Modular.Structures where

open import Untyped.Relation.Binary
open import Untyped.Relation.Binary.Modular
open import Untyped.Relation.Binary.Modular.Patterns
```

## Structures

If a relation has the `CompatTerm` rules, then it forms a `TermCompatible` structure.

```
CompatTerm-TermCompatible : ∀ {R : Relation} → CompatTerm R ⊆ R → TermCompatible R
CompatTerm-TermCompatible inj = record
  { compat-var     = inj (compat-varF _)
  ; compat-ƛ       = λ RM → inj (compat-lambdaF RM)
  ; compat-·       = λ RM RN → inj (compat-applyF RM RN)
  ; compat-force   = λ RM → inj (compat-forceF RM)
  ; compat-delay   = λ RM → inj (compat-delayF RM)
  ; compat-constr  = λ RMS → inj (compat-constrF RMS)
  ; compat-case    = λ RM RMS → inj (compat-caseF RM RMS)
  ; compat-con     = inj compat-conF
  ; compat-builtin = inj compat-builtinF
  ; compat-error   = inj compat-errorF
  }
```
