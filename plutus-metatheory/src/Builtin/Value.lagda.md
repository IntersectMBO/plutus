---
title: Builtin.Value
layout: page
---

This module defines the builtin type `Value`, and the semantics of the builtin
functions on it. Each builtin function is defined by the Agda function of the same
name, whose description starts with **Builtin.**:

* `insertCoin`, `lookupCoin`, `unionValue`, `valueContains` and `scaleValue`;
* `policies`, `assetCount`, `keepPolicies` and `dropPolicies`;
* `valueData` and `unValueData`.

A builtin function that can fail returns a `Maybe`, and fails when it returns `nothing`.

```
module Builtin.Value where
```

## Imports

```
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All; []; all?)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ; 0ℤ; +_; -_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; _^_; _∸_; s≤s; z≤n)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬?; _×-dec_)
open import Relation.Nullary.Decidable using (True; toWitness)

import Data.Integer as ℤ
import Data.List as List
import Data.Maybe as Maybe
import Data.Nat as ℕ
import Builtin.ByteString.Base as BS
import Relation.Unary as U
import Builtin.Data as D

open import Builtin.Binary using (natToByte)
open import Builtin.ByteString.Base using (ByteString; length)
open import Data.List.Membership.DecPropositional BS._≟_ using (_∈?_; _∉?_)
open import Builtin.Value.Base
open import Builtin.Value.Data using (valueData∞; unValueData∞)
open import Builtin.Value.Nested using (toNested∞)
open import Builtin.Value.Union using (mergeEntries-all; merge∞)
```

## Values within the builtin bounds

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

valid-keys? : (e : Entry) → Dec (ValidKeys e)
valid-keys? ((c , t) , _) = valid-key? c ×-dec valid-key? t
```

`fromValue∞ v` checks that the quantities of `v`, whose keys are valid, are in range.

```
fromValue∞ : (v : Value∞) → .(All ValidKeys (Value∞.map v)) → Maybe Value
fromValue∞ v k with all? (in-range? ∘ proj₂) (Value∞.map v)
... | yes r = just (mkValue v k r)
... | no  _ = nothing
```

## Setting, removing and looking up tokens

`insert`, `filterValue` and `delete` are the corresponding operations on `Value∞`.
`insert` also requires the key to be valid and the quantity to be in range.
`filterValue`, and so `delete`, keeps the bounds, since it only removes entries.

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

filterValue : ∀ {P : Key → Set} → U.Decidable P → Value → Value
filterValue P? (mkValue v k r) =
  mkValue
    (filter∞ P? v)
    (filterEntries-all P? (Value∞.map v) k)
    (filterEntries-all P? (Value∞.map v) r)

delete : CurrencySymbol → TokenName → Value → Value
delete c t = filterValue λ k → ¬? (k ≟ᵏ (c , t))
```

**Builtin.** `lookupCoin c t v` is the quantity of the token `t` of the currency `c` in
`v`, or zero if `v` does not contain it. It has no conditions on its keys: a key that is
too long cannot be in a value, so its quantity is zero.

```
lookupCoin : CurrencySymbol → TokenName → Value → Quantity
lookupCoin c t = lookup∞ c t ∘ value∞
```

**Builtin.** `insertCoin c t q v` sets the quantity of the token `t` of the currency `c`
in `v` to `q`. If `q` is zero, it deletes the token and succeeds, whatever the lengths
of `c` and `t`. Otherwise, it fails unless `c` and `t` are valid and `q` is in range.

```
insertCoin : CurrencySymbol → TokenName → Quantity → Value → Maybe Value
insertCoin c t q v with q ℤ.≟ 0ℤ
... | yes _   = just (delete c t v)
... | no  q≢0 with valid-key? c | valid-key? t | in-range? q
...   | yes vc | yes vt | yes r = just (insert c vc t vt q q≢0 r v)
...   | _      | _      | _     = nothing
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

**Builtin.** `unionValue v₁ v₂` adds the quantities of `v₁` and `v₂` token by token. It
fails if one of the resulting quantities is not a signed 128-bit integer; its keys are
those of `v₁` and `v₂`, so they are valid. The quantities of tokens in only one of the
values are already in range, so this happens exactly when the sum of the quantities of a
token in both values is out of range.

```
unionValue : Value → Value → Maybe Value
unionValue (mkValue v₁ k₁ _) (mkValue v₂ k₂ _) =
  fromValue∞
    (merge∞ v₁ v₂)
    (mergeEntries-all (λ vk _ _ → vk) (Value∞.map v₁) (Value∞.map v₂) k₁ k₂)
```

Because of this, `unionValue` is commutative and has `empty` as its identity, but it is
not associative: with `q` the maximum quantity, `(q + 1) - 1` fails, since `q + 1` is out
of range, while `q + (1 - 1)` is `q`. The sum of values without the range condition,
`merge∞`, is associative.

```
private
  big one minusOne : Value
  big      = ins c₁ c₁ maxQuantity empty
  one      = ins c₁ c₁ (+ 1) empty
  minusOne = ins c₁ c₁ (- (+ 1)) empty

  _ : (unionValue big one Maybe.>>= λ x → unionValue x minusOne) ≡ nothing
  _ = refl

  _ : (unionValue one minusOne Maybe.>>= unionValue big) ≡ just big
  _ = refl
```

**Builtin.** `scaleValue n v` multiplies every quantity of `v` by `n`, which may be any
integer. It fails if one of the products is not a signed 128-bit integer; scaling keeps
the keys, so they are valid. Scaling by zero gives the empty value, whatever `v` is.

```
scaleValue : ℤ → Value → Maybe Value
scaleValue n (mkValue v k _) =
  fromValue∞
    (scale∞ n v)
    (scale∞-keys {P = λ (c , t) → ValidKey c × ValidKey t} n v k)
```

**Builtin.** `valueContains v₁ v₂` checks that `v₁` holds at least as much of every token
as `v₂` does. It fails if either value has a negative quantity. In particular, if `v₁` and
`v₂` have no tokens in common, `v₁` contains `v₂` only if `v₂` is empty.

```
valueContains : Value → Value → Maybe Bool
valueContains v₁ v₂
  with nonNegative? (Value∞.map (value∞ v₁)) ×-dec nonNegative? (Value∞.map (value∞ v₂))
... | yes _ = just (contains∞ (value∞ v₁) (value∞ v₂))
... | no  _ = nothing
```

## Policies and asset counts

**Builtin.** `policies v` lists the currency symbols of `v`, in increasing order, each
once.

```
policies : Value → List CurrencySymbol
policies = List.map proj₁ ∘ toNested∞ ∘ value∞
```

**Builtin.** `assetCount v` is the number of tokens of `v`.

```
assetCount : Value → ℤ
assetCount v = + List.length (Value∞.map (value∞ v))
```

**Builtin.** `keepPolicies ps v` keeps the tokens of `v` whose currency symbol is in `ps`,
and `dropPolicies ps v` the others (see `Builtin.Value.Base`). Currency symbols in `ps`
that are not in `v`, including those that are too long, have no effect. Both only remove
tokens, so they keep the bounds, but they fail if `ps` has more than `policyFilterMaxIds`
elements, counting repetitions.

```
policyFilterMaxIds : ℕ
policyFilterMaxIds = 256

keepPolicies : List CurrencySymbol → Value → Maybe Value
keepPolicies ps v with List.length ps ℕ.≤? policyFilterMaxIds
... | yes _ = just (filterValue (λ (c , _) → c ∈? ps) v)
... | no  _ = nothing

dropPolicies : List CurrencySymbol → Value → Maybe Value
dropPolicies ps v with List.length ps ℕ.≤? policyFilterMaxIds
... | yes _ = just (filterValue (λ (c , _) → c ∉? ps) v)
... | no  _ = nothing
```

## Conversion to and from Data

**Builtin.** `valueData v` encodes `v` as `Data`, as `valueData∞` does (see
`Builtin.Value.Data`). It fails if `v` has more than `valueDataMaxSize` tokens.

```
valueDataMaxSize : ℕ
valueDataMaxSize = 40000

valueData : Value → Maybe D.Data
valueData v with List.length (Value∞.map (value∞ v)) ℕ.≤? valueDataMaxSize
... | yes _ = just (valueData∞ (value∞ v))
... | no  _ = nothing
```

`checkBounds v` checks that a `Value∞` fits the bounds of the builtin type.

```
checkBounds : Value∞ → Maybe Value
checkBounds v with all? valid-keys? (Value∞.map v)
... | yes k = fromValue∞ v k
... | no  _ = nothing
```

**Builtin.** `unValueData d` decodes a value from `d`, as `unValueData∞` does. It has no
limit on the size of the value, but fails if one of its keys is too long or one of its
quantities is out of range.

```
unValueData : D.Data → Maybe Value
unValueData d = unValueData∞ d >>= checkBounds
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
  _ : lookupCoin c₁ c₂ v ≡ + 1
  _ = refl

  _ : lookupCoin c₁ c₁ v ≡ - (+ 3)
  _ = refl

  -- Looking up an absent token gives zero, even if its currency is present.
  _ : lookupCoin c₁ c₀ v ≡ 0ℤ
  _ = refl

  _ : lookupCoin c₀ c₀ empty ≡ 0ℤ
  _ = refl

  -- A deleted token is absent.
  _ : lookupCoin c₁ c₂ (delete c₁ c₂ v) ≡ 0ℤ
  _ = refl

  w : Value
  w = ins c₂ c₂ (+ 2) (ins c₁ c₁ (+ 3) empty)

  -- Quantities of the same token are added, and tokens whose sum is zero are dropped.
  _ : Maybe.map toFlatList (unionValue v w)
      ≡ just ((c₁ , c₂ , + 1) ∷ (c₂ , c₀ , + 5) ∷ (c₂ , c₂ , + 2) ∷ [])
  _ = refl

  _ : Maybe.map toFlatList (unionValue w v) ≡ Maybe.map toFlatList (unionValue v w)
  _ = refl

  _ : Maybe.map toFlatList (unionValue empty v) ≡ just (toFlatList v)
  _ = refl

  -- A sum out of range fails.
  _ : Maybe.map toFlatList (unionValue big big) ≡ nothing
  _ = refl

  _ : Maybe.map toFlatList (unionValue big minusOne)
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

  -- A value with non-negative quantities.
  p : Value
  p = ins c₂ c₀ (+ 5) (ins c₁ c₂ (+ 1) (ins c₁ c₁ (+ 3) empty))

  -- Every value contains the empty value and itself.
  _ : valueContains p empty ≡ just true
  _ = refl

  _ : valueContains p p ≡ just true
  _ = refl

  _ : valueContains empty empty ≡ just true
  _ = refl

  -- Smaller quantities of some of the tokens are contained.
  _ : valueContains p (ins c₂ c₀ (+ 4) (ins c₁ c₂ (+ 1) empty)) ≡ just true
  _ = refl

  -- A larger quantity is not.
  _ : valueContains p (ins c₂ c₀ (+ 6) empty) ≡ just false
  _ = refl

  -- Neither is a token that is absent, even if its currency is present.
  _ : valueContains p (ins c₁ c₀ (+ 1) empty) ≡ just false
  _ = refl

  _ : valueContains empty p ≡ just false
  _ = refl

  -- Values with no tokens in common don't contain each other, unless one is empty.
  _ : valueContains p (ins c₀ c₀ (+ 1) empty) ≡ just false
  _ = refl

  _ : valueContains (ins c₀ c₀ (+ 1) empty) p ≡ just false
  _ = refl

  -- A negative quantity in either value fails, even if it is not compared.
  _ : valueContains v empty ≡ nothing
  _ = refl

  _ : valueContains p (ins c₁ c₁ (- (+ 1)) empty) ≡ nothing
  _ = refl

  -- Scaling multiplies every quantity, and keeps the keys.
  _ : Maybe.map toFlatList (scaleValue (+ 2) v)
      ≡ just ((c₁ , c₁ , - (+ 6)) ∷ (c₁ , c₂ , + 2) ∷ (c₂ , c₀ , + 10) ∷ [])
  _ = refl

  _ : Maybe.map toFlatList (scaleValue (- (+ 2)) v)
      ≡ just ((c₁ , c₁ , + 6) ∷ (c₁ , c₂ , - (+ 2)) ∷ (c₂ , c₀ , - (+ 10)) ∷ [])
  _ = refl

  -- Scaling by zero gives the empty value.
  _ : Maybe.map toFlatList (scaleValue 0ℤ v) ≡ just []
  _ = refl

  -- Scaling the empty value succeeds, even by a factor out of range.
  _ : Maybe.map toFlatList (scaleValue (+ (2 ^ 200)) empty) ≡ just []
  _ = refl

  -- Products out of range fail, at both ends of the range.
  _ : Maybe.map toFlatList (scaleValue (+ 2) (ins c₁ c₁ (+ (2 ^ 126)) empty)) ≡ nothing
  _ = refl

  _ : Maybe.map toFlatList (scaleValue (+ 2) (ins c₁ c₁ (- (+ (2 ^ 126))) empty))
      ≡ just ((c₁ , c₁ , minQuantity) ∷ [])
  _ = refl

  _ : Maybe.map toFlatList (scaleValue (+ 2) (ins c₁ c₁ (- (+ (2 ^ 126 ℕ.+ 1))) empty))
      ≡ nothing
  _ = refl

  _ : Maybe.map toFlatList (scaleValue (- (+ 1)) (ins c₁ c₁ minQuantity empty)) ≡ nothing
  _ = refl

  -- Values are encoded as maps of maps, grouped by currency symbol.
  _ : valueData empty ≡ just (D.Map [])
  _ = refl

  _ : valueData p
      ≡ just (D.Map ( (D.B c₁ , D.Map ((D.B c₁ , D.I (+ 3)) ∷ (D.B c₂ , D.I (+ 1)) ∷ []))
                    ∷ (D.B c₂ , D.Map ((D.B c₀ , D.I (+ 5)) ∷ []))
                    ∷ []))
  _ = refl

  -- Negative quantities are encoded too.
  _ : valueData (ins c₁ c₁ (- (+ 1)) empty)
      ≡ just (D.Map ((D.B c₁ , D.Map ((D.B c₁ , D.I (- (+ 1))) ∷ [])) ∷ []))
  _ = refl

  -- Decoding an encoded value gives it back.
  _ : (valueData v >>= unValueData) ≡ just v
  _ = refl

  _ : (valueData p >>= unValueData) ≡ just p
  _ = refl

  _ : unValueData (D.Map []) ≡ just empty
  _ = refl

  -- An encoding of a single token.
  tok : ByteString → ByteString → ℤ → D.Data × D.Data
  tok c t q = D.B c , D.Map ((D.B t , D.I q) ∷ [])

  -- Decoding fails on other shapes of data.
  _ : unValueData (D.List []) ≡ nothing
  _ = refl

  _ : unValueData (D.Map ((D.I (+ 1) , D.Map []) ∷ [])) ≡ nothing
  _ = refl

  _ : unValueData (D.Map ((D.B c₁ , D.List []) ∷ [])) ≡ nothing
  _ = refl

  _ : unValueData (D.Map ((D.B c₁ , D.Map ((D.B c₁ , D.B c₁) ∷ [])) ∷ [])) ≡ nothing
  _ = refl

  -- It fails on repeated or unsorted currency symbols, even if their tokens differ.
  _ : unValueData (D.Map (tok c₁ c₁ (+ 1) ∷ tok c₁ c₂ (+ 1) ∷ [])) ≡ nothing
  _ = refl

  _ : unValueData (D.Map (tok c₂ c₁ (+ 1) ∷ tok c₁ c₁ (+ 1) ∷ [])) ≡ nothing
  _ = refl

  -- It fails on repeated or unsorted token names.
  _ : unValueData
        (D.Map ((D.B c₁ , D.Map ((D.B c₁ , D.I (+ 1)) ∷ (D.B c₁ , D.I (+ 2)) ∷ [])) ∷ []))
      ≡ nothing
  _ = refl

  _ : unValueData
        (D.Map ((D.B c₁ , D.Map ((D.B c₂ , D.I (+ 1)) ∷ (D.B c₁ , D.I (+ 2)) ∷ [])) ∷ []))
      ≡ nothing
  _ = refl

  -- It fails on a currency symbol without tokens.
  _ : unValueData (D.Map ((D.B c₁ , D.Map []) ∷ [])) ≡ nothing
  _ = refl

  -- It fails on zero quantities, and quantities out of range.
  _ : unValueData (D.Map (tok c₁ c₁ 0ℤ ∷ [])) ≡ nothing
  _ = refl

  _ : unValueData (D.Map (tok c₁ c₁ (maxQuantity ℤ.+ + 1) ∷ [])) ≡ nothing
  _ = refl

  _ : unValueData (D.Map (tok c₁ c₁ (minQuantity ℤ.- + 1) ∷ [])) ≡ nothing
  _ = refl

  -- Keys may be up to 32 bytes long.
  k₃₂ k₃₃ : ByteString
  k₃₂ = BS.replicate 32 (natToByte 1 (s≤s (s≤s z≤n)))
  k₃₃ = BS.replicate 33 (natToByte 1 (s≤s (s≤s z≤n)))

  _ : Maybe.map toFlatList (unValueData (D.Map (tok k₃₂ c₁ (+ 1) ∷ [])))
      ≡ just ((k₃₂ , c₁ , + 1) ∷ [])
  _ = refl

  _ : unValueData (D.Map (tok k₃₃ c₁ (+ 1) ∷ [])) ≡ nothing
  _ = refl

  _ : unValueData (D.Map (tok c₁ k₃₃ (+ 1) ∷ [])) ≡ nothing
  _ = refl

  -- Policies are listed in increasing order, each once, including the empty currency
  -- symbol.
  _ : policies v ≡ c₁ ∷ c₂ ∷ []
  _ = refl

  _ : policies (ins c₀ c₂ (+ 1) (ins c₂ c₁ (+ 1) v)) ≡ c₀ ∷ c₁ ∷ c₂ ∷ []
  _ = refl

  _ : policies empty ≡ []
  _ = refl

  -- `insertCoin` sets a quantity, and deletes the token if it is zero.
  _ : Maybe.map toFlatList (insertCoin c₁ c₂ (+ 7) v)
      ≡ just ((c₁ , c₁ , - (+ 3)) ∷ (c₁ , c₂ , + 7) ∷ (c₂ , c₀ , + 5) ∷ [])
  _ = refl

  _ : Maybe.map toFlatList (insertCoin c₁ c₂ 0ℤ v)
      ≡ just ((c₁ , c₁ , - (+ 3)) ∷ (c₂ , c₀ , + 5) ∷ [])
  _ = refl

  -- Deleting does not check the keys, but inserting does.
  _ : Maybe.map toFlatList (insertCoin k₃₃ c₁ 0ℤ v) ≡ just (toFlatList v)
  _ = refl

  _ : Maybe.map toFlatList (insertCoin k₃₃ c₁ (+ 1) v) ≡ nothing
  _ = refl

  _ : Maybe.map toFlatList (insertCoin c₁ k₃₃ (+ 1) v) ≡ nothing
  _ = refl

  _ : Maybe.map toFlatList (insertCoin k₃₂ k₃₂ (+ 1) empty)
      ≡ just ((k₃₂ , k₃₂ , + 1) ∷ [])
  _ = refl

  -- Quantities out of range fail.
  _ : Maybe.map toFlatList (insertCoin c₁ c₁ (maxQuantity ℤ.+ + 1) v) ≡ nothing
  _ = refl

  _ : lookupCoin c₂ c₀ v ≡ + 5
  _ = refl

  -- `assetCount` counts tokens, not currencies.
  _ : assetCount v ≡ + 3
  _ = refl

  _ : assetCount empty ≡ 0ℤ
  _ = refl

  -- Keeping and dropping policies, ignoring absent or invalid ones and repetitions.
  _ : Maybe.map toFlatList (keepPolicies (c₁ ∷ k₃₃ ∷ c₀ ∷ c₁ ∷ []) v)
      ≡ just ((c₁ , c₁ , - (+ 3)) ∷ (c₁ , c₂ , + 1) ∷ [])
  _ = refl

  _ : Maybe.map toFlatList (dropPolicies (c₁ ∷ k₃₃ ∷ c₀ ∷ c₁ ∷ []) v)
      ≡ just ((c₂ , c₀ , + 5) ∷ [])
  _ = refl

  _ : Maybe.map toFlatList (keepPolicies [] v) ≡ just []
  _ = refl

  _ : Maybe.map toFlatList (dropPolicies [] v) ≡ just (toFlatList v)
  _ = refl

  -- Up to 256 policy ids are allowed, counting repetitions.
  _ : Maybe.map toFlatList (keepPolicies (List.replicate 256 c₂) v)
      ≡ just ((c₂ , c₀ , + 5) ∷ [])
  _ = refl

  _ : Maybe.map toFlatList (keepPolicies (List.replicate 257 c₂) v) ≡ nothing
  _ = refl

  _ : Maybe.map toFlatList (dropPolicies (List.replicate 257 c₂) empty) ≡ nothing
  _ = refl
```
