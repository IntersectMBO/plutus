---
title: Untyped.Relation.Binary.Modular.Patterns
layout: page
---

Convenient pattern synonyms for matching on modular relation constructors.

```
module Untyped.Relation.Binary.Modular.Patterns where

open import Untyped.Relation.Binary.Modular
```

## Pattern synonyms

```
pattern inj₀ p = inl p
pattern inj₁ p = inr (inj₀ p)
pattern inj₂ p = inr (inj₁ p)
pattern inj₃ p = inr (inj₂ p)
pattern inj₄ p = inr (inj₃ p)
pattern inj₅ p = inr (inj₄ p)
pattern inj₆ p = inr (inj₅ p)
pattern inj₇ p = inr (inj₆ p)
pattern inj₈ p = inr (inj₇ p)
pattern inj₉ p = inr (inj₈ p)

pattern compat-varF n     = inj₀ (`F n)
pattern compat-lambdaF p  = inj₁ (ƛF p)
pattern compat-applyF p q = inj₂ (p ·F q)
pattern compat-forceF p   = inj₃ (forceF p)
pattern compat-delayF p   = inj₄ (delayF p)
pattern compat-conF       = inj₅ conF
pattern compat-constrF p  = inj₆ (constrF p)
pattern compat-caseF p q  = inj₇ (caseF p q)
pattern compat-builtinF   = inj₈ builtinF
pattern compat-errorF     = inj₉ errorF
```
