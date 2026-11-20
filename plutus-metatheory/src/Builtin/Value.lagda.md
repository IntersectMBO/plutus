---
title: Builtin.Value
layout: page
---

```
module Builtin.Value where
```

## Imports

```
open import Builtin.ByteString.Base using (ByteString; _<ᵇ_)
open import Data.List using (List; _∷_; [])
import Data.List as List 
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Integer using (ℤ; _≟_; 0ℤ)
open import Data.Bool using (T; Bool; true; false; if_then_else_; not; _∧_)
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable using (does)

```

## Value

```
CurrencySymbol : Set
CurrencySymbol = ByteString

TokenName : Set
TokenName = ByteString

Quantity : Set
Quantity = ℤ

<-keysᵇ : {A : Set} → List (ByteString × A) → Bool
<-keysᵇ = go ∘ List.map proj₁
  where
    go : List ByteString → Bool
    go []       = true
    go (x ∷ []) = true
    go (k ∷ tail@((k' ∷ _))) =
      if k <ᵇ k' then go tail else false

quantity-≢-zeroᵇ : List (ByteString × Quantity) → Bool
quantity-≢-zeroᵇ =
  List.foldr (λ (_ , q) acc → not (does (q ≟ 0ℤ)) ∧ acc) true

not-emptyᵇ : List (ByteString × Quantity) → Bool
not-emptyᵇ = not ∘ List.null

record TokenMap : Set where
  constructor mkTokenMap
  field
    map : List (TokenName × Quantity)
    .<-keys : T (<-keysᵇ map)
    .quantity-≢-zero : T (quantity-≢-zeroᵇ map)
    .not-empty : T (not-emptyᵇ map)

record Value : Set where
  constructor mkValue
  field
    map : List (CurrencySymbol × TokenMap)
    .<-keys : T (<-keysᵇ map)
```
