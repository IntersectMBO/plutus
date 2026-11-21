---
title: Builtin.Value.Base
layout: page
---

This module defines `Value∞` is the mathematical object behind the builtin `Value`
type defined in `Builtin.Value`.

```
module Builtin.Value.Base where
```

## Imports

```
open import Data.List using (List; _∷_; [])
open import Data.Bool using (Bool)
open import Data.List.Relation.Unary.All
  using (All; []; _∷_; all?) renaming (map to All-map)
open import Data.List.Relation.Unary.Linked using (Linked; []; [-]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-isStrictTotalOrder)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise; ≡×≡⇒≡)
open import Data.Integer using (ℤ; 0ℤ)
open import Data.Maybe using (maybe′)
open import Data.Sum using ([_,_]′)
open import Function.Base using (_∘_; _on_)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Nullary using (Dec; yes; no; ¬?; isYes)

import Data.Integer as ℤ
import Data.Integer.Properties as ℤ
import Data.List as List
import Data.List.Relation.Unary.All.Properties as All
import Data.List.Relation.Unary.Linked.Properties as Linked
import Relation.Unary as U
import Builtin.ByteString.Base as BS
import Builtin.ByteString.Order as BS

open import Builtin.ByteString.Base using (ByteString)
open import Data.List.Membership.DecPropositional BS._≟_ using (_∈?_; _∉?_)
```

## Values

A value is a finitely supported map from pairs of a currency symbol and a token name to
an integer quantity. We represent it as a flat association list from such pairs, which we
call *keys*, to quantities. The list is required to be *well-formed*, so that every value
has exactly one representation:

* the keys are strictly increasing (so there are no duplicates);
* every quantity is non-zero.

ByteStrings are ordered lexicographically, as described in `Builtin.ByteString.Order`,
and keys are ordered lexicographically by currency symbol, then by token name. A
well-formed list therefore contains the tokens of each currency next to each other, in
increasing order, and grouping them by currency gives the nested association list used
as the concrete representation of values, in which every inner list is non-empty (see
`Builtin.Value.Nested`).

`Value∞` places no bound on the lengths of keys or on quantities; the bounds of the
builtin type are imposed in `Builtin.Value`. This makes adding and negating values
total, and gives them the structure of a commutative group (see
`Builtin.Value.Union.Properties`).

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

NonZero : List Entry → Set
NonZero = All (λ e → proj₂ e ≢ 0ℤ)

record Value∞ : Set where
  constructor mkValue∞
  field
    map : List Entry
    .<-keys : Linked _<ᵉ_ map
    .quantity-≢-zero : NonZero map

empty∞ : Value∞
empty∞ = mkValue∞ [] [] []
```

Being non-zero is decidable.

```
≢-zero? : (q : Quantity) → Dec (q ≢ 0ℤ)
≢-zero? q = ¬? (q ℤ.≟ 0ℤ)

nonZero? : ∀ kvs → Dec (NonZero kvs)
nonZero? = all? (≢-zero? ∘ proj₂)
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

Sortedness only depends on the keys, so the quantity of the first entry of a sorted list
can be replaced.

```
replace-head
  : ∀ {k q q' kvs} → Linked _<ᵉ_ ((k , q') ∷ kvs) → Linked _<ᵉ_ ((k , q) ∷ kvs)
replace-head [-]     = [-]
replace-head (r ∷ l) = r ∷ l
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

`insert∞ c t q v` sets the quantity of the token `t` of the currency `c` in `v` to `q`,
replacing the previous quantity, if any. `q` must be non-zero: setting a quantity to zero
amounts to deleting the token, which is done by `delete∞` (see below).

```
insert∞ : CurrencySymbol → TokenName → (q : Quantity) → .(q ≢ 0ℤ) → Value∞ → Value∞
insert∞ c t q nz (mkValue∞ m s z) =
  mkValue∞
    (insertEntry (c , t) q m)
    (insertEntry-linked (c , t) q m s)
    (insertEntry-all (c , t) q m z nz)
```

## Filtering

`filter∞ P? v` keeps the tokens of `v` whose key satisfies the decidable property `P`.
Removing entries from a list keeps it sorted and keeps every property of all its
entries, so the result is well-formed.

```
filterEntries : ∀ {P : Key → Set} → U.Decidable P → List Entry → List Entry
filterEntries P? = List.filter (P? ∘ proj₁)

filterEntries-linked
  : ∀ {P : Key → Set} (P? : U.Decidable P) kvs
  → Linked _<ᵉ_ kvs → Linked _<ᵉ_ (filterEntries P? kvs)
-- `<ᵉ-trans` is eta-expanded, as its implicit entries can't be inferred through `proj₁`
-- once `_<ᵉ_` unfolds.
filterEntries-linked P? _ =
  Linked.filter⁺ (P? ∘ proj₁) (λ {e₁ e₂ e₃} → <ᵉ-trans {e₁} {e₂} {e₃})

filterEntries-all
  : ∀ {P : Key → Set} {Q : Entry → Set} (P? : U.Decidable P) kvs
  → All Q kvs → All Q (filterEntries P? kvs)
filterEntries-all P? _ = All.filter⁺ (P? ∘ proj₁)

filter∞ : ∀ {P : Key → Set} → U.Decidable P → Value∞ → Value∞
filter∞ P? (mkValue∞ m s z) =
  mkValue∞ (filterEntries P? m) (filterEntries-linked P? m s) (filterEntries-all P? m z)
```

`delete∞ c t v` removes the token `t` of the currency `c` from `v`, if it is present.

```
delete∞ : CurrencySymbol → TokenName → Value∞ → Value∞
delete∞ c t = filter∞ λ k → ¬? (k ≟ᵏ (c , t))
```

`keepPolicies∞ ps v` keeps the tokens of `v` whose currency symbol is in `ps`, and
`dropPolicies∞ ps v` the others.

```
keepPolicies∞ : List CurrencySymbol → Value∞ → Value∞
keepPolicies∞ ps = filter∞ λ k → proj₁ k ∈? ps

dropPolicies∞ : List CurrencySymbol → Value∞ → Value∞
dropPolicies∞ ps = filter∞ λ k → proj₁ k ∉? ps
```

## Lookup

`lookup∞ c t v` is the quantity of the token `t` of the currency `c` in `v`, or zero if
`v` does not contain it. Since the quantities in a value are non-zero, a quantity of
zero means exactly that the token is absent.

```
lookupEntry : Key → List Entry → Quantity
lookupEntry k kvs = maybe′ proj₂ 0ℤ (List.find (λ e → proj₁ e ≟ᵏ k) kvs)

lookup∞ : CurrencySymbol → TokenName → Value∞ → Quantity
lookup∞ c t v = lookupEntry (c , t) (Value∞.map v)
```

## Scaling

`scale∞ n v` multiplies every quantity of `v` by `n`. Scaling by zero gives the empty
value. Otherwise, scaling keeps the keys, so it keeps them sorted, and the product of two
non-zero integers is non-zero.

```
scaleEntry : Quantity → Entry → Entry
scaleEntry n (k , q) = k , n ℤ.* q

scaleEntries : Quantity → List Entry → List Entry
scaleEntries n = List.map (scaleEntry n)

scale∞ : Quantity → Value∞ → Value∞
scale∞ n (mkValue∞ m s z) with n ℤ.≟ 0ℤ
... | yes _   = empty∞
... | no  n≢0 =
  mkValue∞
    (scaleEntries n m)
    (Linked.map⁺ {R = _<ᵉ_} {f = scaleEntry n} s)
    (All.map⁺ (All-map (λ q≢0 → [ n≢0 , q≢0 ]′ ∘ ℤ.i*j≡0⇒i≡0∨j≡0 n) z))
```

Scaling keeps every property of the keys.

```
scale∞-keys
  : ∀ {P : Key → Set} n v
  → All (P ∘ proj₁) (Value∞.map v) → All (P ∘ proj₁) (Value∞.map (scale∞ n v))
scale∞-keys n (mkValue∞ m _ _) a with n ℤ.≟ 0ℤ
... | yes _ = []
... | no  _ = All.map⁺ a
```

## Negation

`negate∞ v` negates every quantity of `v`. Negative quantities are meaningful: for
example, the tokens minted by a transaction are given as a value, in which burnt tokens
have negative quantities. Negation is scaling by `-1`.

```
negate∞ : Value∞ → Value∞
negate∞ = scale∞ ℤ.-1ℤ
```

## Containment

`contains∞ v₁ v₂` checks that `v₁` contains `v₂`, that is, that every entry `(k , q)` of
`v₂` has `q ≤ lookupEntry k` in `v₁`. When the quantities of `v₁` are non-negative, this
means that `v₁` holds at least as much of every token as `v₂` does (see
`Builtin.Value.Base.Properties`). The builtin requires the quantities of both values to
be non-negative.

```
ContainsEntries : List Entry → List Entry → Set
ContainsEntries kvs₁ = All (λ e → proj₂ e ℤ.≤ lookupEntry (proj₁ e) kvs₁)

containsEntries? : ∀ kvs₁ kvs₂ → Dec (ContainsEntries kvs₁ kvs₂)
containsEntries? kvs₁ = all? (λ e → proj₂ e ℤ.≤? lookupEntry (proj₁ e) kvs₁)

contains∞ : Value∞ → Value∞ → Bool
contains∞ v₁ v₂ = isYes (containsEntries? (Value∞.map v₁) (Value∞.map v₂))

NonNegative : List Entry → Set
NonNegative = All (λ e → 0ℤ ℤ.≤ proj₂ e)

nonNegative? : ∀ kvs → Dec (NonNegative kvs)
nonNegative? = all? (λ e → 0ℤ ℤ.≤? proj₂ e)
```

## Conversion

`toFlatList∞` forgets the invariants, giving the entries of a value as a flat list of
triples.

```
toFlatList∞ : Value∞ → List (CurrencySymbol × TokenName × Quantity)
toFlatList∞ v = List.map (λ ((c , t) , q) → c , t , q) (Value∞.map v)
```
