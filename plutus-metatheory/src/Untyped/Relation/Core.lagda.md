---
title: Untyped.Relation.Core
layout: page
---
```
module Untyped.Relation.Core where

open import Untyped
```

## Binary relations on untyped terms

```
Relation : Set₁
Relation = ∀{X} → X ⊢ → X ⊢ → Set
```

## Relation transformers

Relation transformers are relations parametrised by other relations, such that
the parameter may only be used in strictly positive positions. This is useful
for defining inductive relations modularly.

```
RelationT : Set₁
RelationT = @++ Relation → Relation
```
