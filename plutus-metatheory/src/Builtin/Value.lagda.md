---
title: Builtin.Value
layout: page
---

```
module Builtin.Value where
```

## Imports

```
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All; []; all?)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Integer using (ℤ; 0ℤ; +_; -_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _^_; _∸_; s≤s; z≤n)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no; _×-dec_)
open import Relation.Nullary.Decidable using (True; toWitness)

import Data.Integer as ℤ
import Data.Maybe as Maybe
import Data.Nat as ℕ
import Builtin.ByteString.Base as BS

open import Builtin.Binary using (natToByte)
open import Builtin.ByteString.Base using (ByteString; length)
open import Builtin.Value.Base
open import Builtin.Value.Union using (mergeEntries-all; merge∞)
```

## Value

A `Value` is a `Value∞` (see `Builtin.Value.Base`) that fits the bounds of the builtin
type:

* every currency symbol and token name is at most 32 bytes long. (Real currency symbols
  are either empty or 28 bytes long, but any length up to 32 bytes is allowed.)
* every quantity is a signed 128-bit integer, i.e. it lies in the range
  [-2¹²⁷, 2¹²⁷ - 1].

```
maxKeyLen : ℕ
maxKeyLen = 32

ValidKey : ByteString → Set
ValidKey k = length k ℕ.≤ maxKeyLen

ValidKeys : Entry → Set
ValidKeys ((c , t) , _) = ValidKey c × ValidKey t

minQuantity : ℤ
minQuantity = - (+ (2 ^ 127))

maxQuantity : ℤ
maxQuantity = + (2 ^ 127 ∸ 1)

InRange : Quantity → Set
InRange q = minQuantity ℤ.≤ q × q ℤ.≤ maxQuantity

record Value : Set where
  constructor mkValue
  field
    value∞ : Value∞
    .keys-≤-maxKeyLen : All ValidKeys (Value∞.map value∞)
    .quantity-in-range : All (InRange ∘ proj₂) (Value∞.map value∞)

open Value public

empty : Value
empty = mkValue empty∞ [] []
```

The bounds are decidable.

```
valid-key? : (k : ByteString) → Dec (ValidKey k)
valid-key? k = length k ℕ.≤? maxKeyLen

in-range? : (q : Quantity) → Dec (InRange q)
in-range? q = (minQuantity ℤ.≤? q) ×-dec (q ℤ.≤? maxQuantity)
```

`fromValue∞ v` checks that the quantities of `v`, whose keys are valid, are in range.

```
fromValue∞ : (v : Value∞) → .(All ValidKeys (Value∞.map v)) → Maybe Value
fromValue∞ v k with all? (in-range? ∘ proj₂) (Value∞.map v)
... | yes r = just (mkValue v k r)
... | no  _ = nothing
```

## Operations

`insert`, `delete` and `lookup` are the corresponding operations on `Value∞`. `insert`
also requires the key to be valid and the quantity to be in range, and `delete` keeps
the bounds, since it only removes entries. `lookup` has no conditions on its key: a key
that is too long cannot be in a value, so its quantity is zero.

```
insert
  : (c : CurrencySymbol) → .(ValidKey c)
  → (t : TokenName) → .(ValidKey t)
  → (q : Quantity) → .(q ≢ 0ℤ) → .(InRange q)
  → Value
  → Value
insert c vc t vt q nz r (mkValue v k ir) =
  mkValue
    (insert∞ c t q nz v)
    (insertEntry-all (c , t) q (Value∞.map v) k (vc , vt))
    (insertEntry-all (c , t) q (Value∞.map v) ir r)

delete : CurrencySymbol → TokenName → Value → Value
delete c t (mkValue v k ir) =
  mkValue
    (delete∞ c t v)
    (deleteEntry-all (c , t) (Value∞.map v) k)
    (deleteEntry-all (c , t) (Value∞.map v) ir)

lookup : CurrencySymbol → TokenName → Value → Quantity
lookup c t = lookup∞ c t ∘ value∞
```

The examples in this module build values with `ins`, which is `insert` with its side
conditions checked by computation.

```
private
  ins
    : (c t : ByteString) (q : Quantity)
    → {True (valid-key? c)} → {True (valid-key? t)}
    → {True (≢-zero? q)} → {True (in-range? q)}
    → Value → Value
  ins c t q {vc} {vt} {nz} {r} =
    insert c (toWitness vc) t (toWitness vt) q (toWitness nz) (toWitness r)

  c₀ c₁ c₂ : ByteString
  c₀ = BS.[]
  c₁ = natToByte 1 (s≤s (s≤s z≤n)) BS.∷ BS.[]
  c₂ = natToByte 2 (s≤s (s≤s (s≤s z≤n))) BS.∷ BS.[]
```

`union v₁ v₂` adds the quantities of `v₁` and `v₂` token by token. It fails if one of the
resulting quantities is not a signed 128-bit integer; its keys are those of `v₁` and
`v₂`, so they are valid. The quantities of tokens in only one
of the values are already in range, so this happens exactly when the sum of the
quantities of a token in both values is out of range.

```
union : Value → Value → Maybe Value
union (mkValue v₁ k₁ _) (mkValue v₂ k₂ _) =
  fromValue∞
    (merge∞ v₁ v₂)
    (mergeEntries-all (λ vk _ _ → vk) (Value∞.map v₁) (Value∞.map v₂) k₁ k₂)
```

Because of this, `union` is commutative and has `empty` as its identity, but it is not
associative: with `q` the maximum quantity, `(q + 1) - 1` fails, since `q + 1` is out of
range, while `q + (1 - 1)` is `q`. The sum of values without the range condition,
`merge∞`, is associative.

```
private
  big one minusOne : Value
  big      = ins c₁ c₁ maxQuantity empty
  one      = ins c₁ c₁ (+ 1) empty
  minusOne = ins c₁ c₁ (- (+ 1)) empty

  _ : (union big one Maybe.>>= λ x → union x minusOne) ≡ nothing
  _ = refl

  _ : (union one minusOne Maybe.>>= union big) ≡ just big
  _ = refl
```

`toFlatList` forgets the invariants, giving the entries of a `Value` as a flat list of
triples.

```
toFlatList : Value → List (CurrencySymbol × TokenName × Quantity)
toFlatList = toFlatList∞ ∘ value∞
```

Some tests:

```
private
  -- A value with three tokens, inserted out of order.
  v : Value
  v = ins c₂ c₀ (+ 5) (ins c₁ c₂ (+ 1) (ins c₁ c₁ (- (+ 3)) empty))

  -- Keys are kept sorted, whatever the order of insertion.
  _ : toFlatList v ≡ (c₁ , c₁ , - (+ 3)) ∷ (c₁ , c₂ , + 1) ∷ (c₂ , c₀ , + 5) ∷ []
  _ = refl

  -- Inserting an existing token replaces its quantity.
  _ : toFlatList (ins c₁ c₁ (+ 7) (ins c₁ c₁ (+ 1) empty)) ≡ (c₁ , c₁ , + 7) ∷ []
  _ = refl

  -- Deleting a present token removes only that token.
  _ : toFlatList (delete c₁ c₂ v) ≡ (c₁ , c₁ , - (+ 3)) ∷ (c₂ , c₀ , + 5) ∷ []
  _ = refl

  -- Deleting an absent token, even one with a matching currency, changes nothing.
  _ : toFlatList (delete c₁ c₀ v) ≡ toFlatList v
  _ = refl

  -- Deleting every token gives the empty value.
  _ : toFlatList (delete c₂ c₀ (delete c₁ c₂ (delete c₁ c₁ v))) ≡ []
  _ = refl

  -- Looking up a present token gives its quantity.
  _ : lookup c₁ c₂ v ≡ + 1
  _ = refl

  _ : lookup c₁ c₁ v ≡ - (+ 3)
  _ = refl

  -- Looking up an absent token gives zero, even if its currency is present.
  _ : lookup c₁ c₀ v ≡ 0ℤ
  _ = refl

  _ : lookup c₀ c₀ empty ≡ 0ℤ
  _ = refl

  -- A deleted token is absent.
  _ : lookup c₁ c₂ (delete c₁ c₂ v) ≡ 0ℤ
  _ = refl

  w : Value
  w = ins c₂ c₂ (+ 2) (ins c₁ c₁ (+ 3) empty)

  -- Quantities of the same token are added, and tokens whose sum is zero are dropped.
  _ : Maybe.map toFlatList (union v w)
      ≡ just ((c₁ , c₂ , + 1) ∷ (c₂ , c₀ , + 5) ∷ (c₂ , c₂ , + 2) ∷ [])
  _ = refl

  _ : Maybe.map toFlatList (union w v) ≡ Maybe.map toFlatList (union v w)
  _ = refl

  _ : Maybe.map toFlatList (union empty v) ≡ just (toFlatList v)
  _ = refl

  -- A sum out of range fails.
  _ : Maybe.map toFlatList (union big big) ≡ nothing
  _ = refl

  _ : Maybe.map toFlatList (union big minusOne)
      ≡ just ((c₁ , c₁ , + (2 ^ 127 ∸ 2)) ∷ [])
  _ = refl

  -- Negation negates every quantity, and a value plus its negation is empty.
  _ : toFlatList∞ (negate∞ (value∞ v))
      ≡ (c₁ , c₁ , + 3) ∷ (c₁ , c₂ , - (+ 1)) ∷ (c₂ , c₀ , - (+ 5)) ∷ []
  _ = refl

  _ : toFlatList∞ (merge∞ (negate∞ (value∞ v)) (value∞ v)) ≡ []
  _ = refl

  -- The sum of the underlying `Value∞`s is defined, but out of range.
  _ : toFlatList∞ (merge∞ (value∞ big) (value∞ big))
      ≡ (c₁ , c₁ , + (2 ^ 128 ∸ 2)) ∷ []
  _ = refl
```
