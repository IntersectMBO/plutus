---
title: Builtin.Value.Properties
layout: page
---

This module proves properties of the builtin operations on values defined in
`Builtin.Value`.

```
module Builtin.Value.Properties where
```

## Imports

```
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Unary.All using (all?)
open import Data.List.Relation.Unary.Linked using (Linked; linked?)
open import Data.Maybe using (just; nothing; _>>=_)
open import Data.Product using (proj₁; proj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (recompute)

import Data.List as List
import Data.Nat as ℕ
import Data.List.Relation.Unary.Linked.Properties as Linked
import Builtin.ByteString.Order as BS

open import Builtin.Value
open import Builtin.Value.Base
open import Builtin.Value.Data
open import Builtin.Value.Data.Properties
open import Builtin.Value.Nested
open import Builtin.Value.Nested.Properties
```

## Checking the bounds

Checking the bounds of a `Value∞` that fits them gives back the `Value`. The bounds are
irrelevant in a `Value`, so they are recomputed.

```
checkBounds-value∞ : ∀ v → checkBounds (value∞ v) ≡ just v
checkBounds-value∞ (mkValue v k r) with all? valid-keys? (Value∞.map v)
... | no ¬k = ⊥-elim (¬k (recompute (all? valid-keys? (Value∞.map v)) k))
... | yes _ with all? (in-range? ∘ proj₂) (Value∞.map v)
...   | yes _ = refl
...   | no ¬r = ⊥-elim (¬r (recompute (all? (in-range? ∘ proj₂) (Value∞.map v)) r))

checkBounds-just : ∀ {v' v} → checkBounds v' ≡ just v → value∞ v ≡ v'
checkBounds-just {v'} eq with all? valid-keys? (Value∞.map v')
checkBounds-just {v'} eq | yes _ with all? (in-range? ∘ proj₂) (Value∞.map v')
checkBounds-just refl | yes _ | yes _ = refl
checkBounds-just ()   | yes _ | no  _
checkBounds-just ()   | no  _
```

## Policies are sorted

```
policies-sorted : ∀ v → Linked BS._<_ (policies v)
policies-sorted (mkValue (mkValue∞ m s _) _ _) =
  recompute (linked? BS._<?_ _)
    (Linked.map⁺ {R = BS._<_} {f = proj₁} (proj₁ (group-wellFormed m s)))
```

## Conversion to and from Data

Decoding the encoding of a value gives it back: `unValueData∞` inverts `valueData∞` (see
`Builtin.Value.Data.Properties`), and the value fits the bounds.

```
unValueData-valueData : ∀ v d → valueData v ≡ just d → unValueData d ≡ just v
unValueData-valueData v d eq
  with List.length (Value∞.map (value∞ v)) ℕ.≤? valueDataMaxSize
unValueData-valueData v _ refl | yes _ =
  trans (cong (_>>= checkBounds) (unValueData∞-valueData∞ (value∞ v)))
        (checkBounds-value∞ v)
unValueData-valueData v _ ()   | no  _
```

Conversely, data that decodes to a value is its encoding, provided that the value is
small enough to be encoded. Without that condition this fails: `unValueData` has no
limit on the size of values.

```
valueData-unValueData
  : ∀ d v
  → unValueData d ≡ just v
  → List.length (Value∞.map (value∞ v)) ℕ.≤ valueDataMaxSize
  → valueData v ≡ just d
valueData-unValueData d v eq size with unValueData∞ d in e
valueData-unValueData d v eq size | just v'
  with List.length (Value∞.map (value∞ v)) ℕ.≤? valueDataMaxSize
... | yes _    =
  cong just
    (trans (cong valueData∞ (checkBounds-just {v'} {v} eq)) (valueData∞-unValueData∞ d e))
... | no ¬size = ⊥-elim (¬size size)
valueData-unValueData d v () size | nothing
```
