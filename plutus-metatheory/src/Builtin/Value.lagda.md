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
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Linked using (Linked; []; [-]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-isStrictTotalOrder)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise; ≡×≡⇒≡)
open import Data.Integer using (ℤ; 0ℤ; +_; -_)
open import Data.Nat using (ℕ; _^_; _∸_; s≤s; z≤n)
open import Function.Base using (_∘_; _on_)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Nullary using (Dec; ¬?; _×-dec_)
open import Relation.Nullary.Decidable using (True; toWitness)

import Data.Integer as ℤ
import Data.List as List
import Data.List.Relation.Unary.All.Properties as All
import Data.List.Relation.Unary.Linked.Properties as Linked
import Data.Nat as ℕ
import Builtin.ByteString.Base as BS
import Builtin.ByteString.Order as BS

open import Builtin.Binary using (natToByte)
open import Builtin.ByteString.Base using (ByteString; length)
```

## Value

A `Value` is a finitely supported map from pairs of a currency symbol and a token name to
an integer quantity. We represent it as a flat association list from such pairs, which we
call *keys*, to quantities. The list is required to be *well-formed*, so that every value
has exactly one representation:

* the keys are strictly increasing (so there are no duplicates);
* every currency symbol and token name is at most 32 bytes long. (Real currency symbols
  are either empty or 28 bytes long, but any length up to 32 bytes is allowed.)
* every quantity is non-zero;
* every quantity is a signed 128-bit integer, i.e. it lies in the range
  [-2¹²⁷, 2¹²⁷ - 1].

ByteStrings are ordered lexicographically, as described in `Builtin.ByteString.Order`,
and keys are ordered lexicographically by currency symbol, then by token name. A
well-formed list therefore contains the tokens of each currency next to each other, in
increasing order, and grouping them by currency gives the nested association list used
as the concrete representation of values, in which every inner list is non-empty.

```
CurrencySymbol : Set
CurrencySymbol = ByteString

TokenName : Set
TokenName = ByteString

Quantity : Set
Quantity = ℤ

Key : Set
Key = CurrencySymbol × TokenName

Entry : Set
Entry = Key × Quantity

_<ᵏ_ : Key → Key → Set
_<ᵏ_ = ×-Lex _≡_ BS._<_ BS._<_

_<ᵉ_ : Entry → Entry → Set
_<ᵉ_ = _<ᵏ_ on proj₁

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
    map : List Entry
    .<-keys : Linked _<ᵉ_ map
    .keys-≤-maxKeyLen : All ValidKeys map
    .quantity-≢-zero : All (λ e → proj₂ e ≢ 0ℤ) map
    .quantity-in-range : All (InRange ∘ proj₂) map

empty : Value
empty = mkValue [] [] [] [] []
```

The conditions on keys and quantities are decidable.

```
valid-key? : (k : ByteString) → Dec (ValidKey k)
valid-key? k = length k ℕ.≤? maxKeyLen

≢-zero? : (q : Quantity) → Dec (q ≢ 0ℤ)
≢-zero? q = ¬? (q ℤ.≟ 0ℤ)

in-range? : (q : Quantity) → Dec (InRange q)
in-range? q = (minQuantity ℤ.≤? q) ×-dec (q ℤ.≤? maxQuantity)
```

## Comparing keys

The order on keys is a strict total order, since it is the lexicographic product of two
strict total orders. `compareᵏ` decides it, and `_≟ᵏ_` decides equality of keys.

```
<ᵏ-isStrictTotalOrder : IsStrictTotalOrder (Pointwise _≡_ _≡_) _<ᵏ_
<ᵏ-isStrictTotalOrder =
  ×-isStrictTotalOrder BS.<-isStrictTotalOrder BS.<-isStrictTotalOrder

<ᵉ-trans : Transitive _<ᵉ_
<ᵉ-trans = IsStrictTotalOrder.trans <ᵏ-isStrictTotalOrder

_≟ᵏ_ : DecidableEquality Key
_≟ᵏ_ = ≡-dec BS._≟_ BS._≟_

compareᵏ : Trichotomous _≡_ _<ᵏ_
compareᵏ k k' with IsStrictTotalOrder.compare <ᵏ-isStrictTotalOrder k k'
... | tri< a ¬b ¬c = tri< a (¬b ∘ λ { refl → refl , refl }) ¬c
... | tri≈ ¬a b ¬c = tri≈ ¬a (≡×≡⇒≡ b) ¬c
... | tri> ¬a ¬b c = tri> ¬a (¬b ∘ λ { refl → refl , refl }) c
```

## Insertion

`insertEntry k q kvs` sets the quantity at the key `k` in the sorted association list
`kvs` to `q`: if `k` is present its quantity is replaced, and otherwise the entry
`(k , q)` is added at the position that keeps the keys sorted.

```
insertEntry : Key → Quantity → List Entry → List Entry
insertEntry k q [] = (k , q) ∷ []
insertEntry k q ((k' , q') ∷ kvs) with compareᵏ k k'
... | tri< _ _ _ = (k , q) ∷ (k' , q') ∷ kvs
... | tri≈ _ _ _ = (k' , q) ∷ kvs
... | tri> _ _ _ = (k' , q') ∷ insertEntry k q kvs
```

`insertEntry` keeps the keys sorted, and a property of all entries holds after
inserting `(k , q)` if it holds for `(k , q)`.

```
private
  -- Sortedness only depends on the keys.
  replace-head
    : ∀ {k q q' kvs} → Linked _<ᵉ_ ((k , q') ∷ kvs) → Linked _<ᵉ_ ((k , q) ∷ kvs)
  replace-head [-]     = [-]
  replace-head (r ∷ l) = r ∷ l

  insertEntry-linked-∷
    : ∀ {e} k q kvs
    → e <ᵉ (k , q)
    → Linked _<ᵉ_ (e ∷ kvs)
    → Linked _<ᵉ_ (e ∷ insertEntry k q kvs)
  insertEntry-linked-∷ k q []                r _        = r ∷ [-]
  insertEntry-linked-∷ k q ((k' , q') ∷ kvs) r (r' ∷ l) with compareᵏ k k'
  ... | tri< k<k' _ _ = r ∷ k<k' ∷ l
  ... | tri≈ _ refl _ = r' ∷ replace-head l
  ... | tri> _ _ k'<k = r' ∷ insertEntry-linked-∷ k q kvs k'<k l

insertEntry-linked
  : ∀ k q kvs → Linked _<ᵉ_ kvs → Linked _<ᵉ_ (insertEntry k q kvs)
insertEntry-linked k q []                _ = [-]
insertEntry-linked k q ((k' , q') ∷ kvs) l with compareᵏ k k'
... | tri< k<k' _ _ = k<k' ∷ l
... | tri≈ _ refl _ = replace-head l
... | tri> _ _ k'<k = insertEntry-linked-∷ k q kvs k'<k l

insertEntry-all
  : ∀ {P : Entry → Set} k q kvs → All P kvs → P (k , q) → All P (insertEntry k q kvs)
insertEntry-all k q []                _        p = p ∷ []
insertEntry-all k q ((k' , q') ∷ kvs) (p' ∷ a) p with compareᵏ k k'
... | tri< _ _ _    = p ∷ p' ∷ a
... | tri≈ _ refl _ = p ∷ a
... | tri> _ _ _    = p' ∷ insertEntry-all k q kvs a p
```

`insert c t q v` sets the quantity of the token `t` of the currency `c` in `v` to `q`,
replacing the previous quantity, if any. The inputs must satisfy the invariants of
`Value`: `c` and `t` must be at most `maxKeyLen` bytes long, and `q` must be a non-zero
signed 128-bit integer. Setting a quantity to zero amounts to deleting the token, which is
done by `delete`.

```
insert
  : (c : CurrencySymbol) → .(ValidKey c)
  → (t : TokenName) → .(ValidKey t)
  → (q : Quantity) → .(q ≢ 0ℤ) → .(InRange q)
  → Value
  → Value
insert c vc t vt q nz r (mkValue m s k z ir) =
  mkValue
    (insertEntry (c , t) q m)
    (insertEntry-linked (c , t) q m s)
    (insertEntry-all (c , t) q m k (vc , vt))
    (insertEntry-all (c , t) q m z nz)
    (insertEntry-all (c , t) q m ir r)
```

## Deletion

`delete c t v` removes the token `t` of the currency `c` from `v`, if it is present. It
keeps the entries whose key is not `(c , t)`. Removing entries from a list keeps it
sorted and keeps every property of all its entries, so the result is well-formed.

```
-- Whether an entry's key differs from `k`.
≢ᵏ? : (k : Key) (e : Entry) → Dec (proj₁ e ≢ k)
≢ᵏ? k e = ¬? (proj₁ e ≟ᵏ k)

deleteEntry : Key → List Entry → List Entry
deleteEntry k = List.filter (≢ᵏ? k)

delete : CurrencySymbol → TokenName → Value → Value
delete c t (mkValue m s k z ir) =
  mkValue
    (deleteEntry (c , t) m)
    -- `<ᵉ-trans` is eta-expanded, as its implicit entries can't be inferred through
    -- `proj₁` once `_<ᵉ_` unfolds.
    (Linked.filter⁺ (≢ᵏ? (c , t)) (λ {e₁ e₂ e₃} → <ᵉ-trans {e₁} {e₂} {e₃}) s)
    (All.filter⁺ (≢ᵏ? (c , t)) k)
    (All.filter⁺ (≢ᵏ? (c , t)) z)
    (All.filter⁺ (≢ᵏ? (c , t)) ir)
```

## Conversion

`toFlatList` forgets the invariants, giving the entries of a `Value` as a flat list of
triples.

```
toFlatList : Value → List (CurrencySymbol × TokenName × Quantity)
toFlatList v = List.map (λ ((c , t) , q) → c , t , q) (Value.map v)
```

Some tests:

```
private
  -- `insert` on literals, with the side conditions checked by computation.
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

  -- Keys are kept sorted, whatever the order of insertion.
  _ : toFlatList (ins c₂ c₀ (+ 5) (ins c₁ c₂ (+ 1) (ins c₁ c₁ (- (+ 3)) empty)))
      ≡ (c₁ , c₁ , - (+ 3)) ∷ (c₁ , c₂ , + 1) ∷ (c₂ , c₀ , + 5) ∷ []
  _ = refl

  -- Inserting an existing token replaces its quantity.
  _ : toFlatList (ins c₁ c₁ (+ 7) (ins c₁ c₁ (+ 1) empty)) ≡ (c₁ , c₁ , + 7) ∷ []
  _ = refl

  v₃ : Value
  v₃ = ins c₂ c₀ (+ 5) (ins c₁ c₂ (+ 1) (ins c₁ c₁ (- (+ 3)) empty))

  -- Deleting a present token removes only that token.
  _ : toFlatList (delete c₁ c₂ v₃) ≡ (c₁ , c₁ , - (+ 3)) ∷ (c₂ , c₀ , + 5) ∷ []
  _ = refl

  -- Deleting an absent token, even one with a matching currency, changes nothing.
  _ : toFlatList (delete c₁ c₀ v₃) ≡ toFlatList v₃
  _ = refl

  -- Deleting every token gives the empty value.
  _ : toFlatList (delete c₂ c₀ (delete c₁ c₂ (delete c₁ c₁ v₃))) ≡ []
  _ = refl
```
