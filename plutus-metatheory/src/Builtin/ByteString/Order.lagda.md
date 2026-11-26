---
title: Builtin.ByteString.Order
layout: page
---

This module defines the order on bytes and the lexicographic order on ByteStrings,
both as relations, `_<_` and `_≤_`, and as the Boolean comparisons `_<ᵇ_` and `_≤ᵇ_`
used by the comparison builtins. The Boolean comparisons are defined from decision
procedures for the relations, so they agree with them by construction.

```
module Builtin.ByteString.Order where
```

## Imports

```
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Definitions
  using (Decidable; Irreflexive; Transitive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; isEquivalence; resp₂)
open import Relation.Binary.Structures
  using (IsStrictPartialOrder; IsStrictTotalOrder; IsDecTotalOrder)
open import Relation.Nullary using (yes; no; does)

import Builtin.Binary as Binary
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ

open import Builtin.Binary using (byteToNat; natToByte; byteToNat-injective)
open import Builtin.ByteString.Base using (ByteString; []; _∷_)
```

## Bytes

Bytes are compared as numbers.

`Byte.<-cmp` first tests the two bytes for equality, bit by bit, and only compares
their numeric values if they differ. This keeps it cheap to evaluate during type
checking: when the bytes are equal, the equality proof is `refl` straight away, rather
than one obtained from the injectivity of `byteToNat`, which only reduces to `refl`
after evaluating the proof of `natToBits-bitsToNat` and this can be very expensive
to compute.

```
module Byte where
  infix 4 _<_

  -- A record rather than a function, so that `x` and `y` can be inferred from `x < y`.
  record _<_ (x y : Binary.Byte) : Set where
    constructor mk<
    field
      <ℕ : byteToNat x ℕ.< byteToNat y

  <-irrefl : Irreflexive _≡_ _<_
  <-irrefl refl (mk< x<x) = ℕ.<-irrefl refl x<x

  <-trans : Transitive _<_
  <-trans (mk< x<y) (mk< y<z) = mk< (ℕ.<-trans x<y y<z)

  <-cmp : Trichotomous _≡_ _<_
  <-cmp x y with x Binary.≟ y
  ... | yes refl = tri≈ (<-irrefl refl) refl (<-irrefl refl)
  ... | no x≢y with ℕ.<-cmp (byteToNat x) (byteToNat y)
  ...   | tri< x<y _ _ = tri< (mk< x<y) x≢y λ { (mk< y<x) → ℕ.<-asym x<y y<x }
  ...   | tri≈ _ x≡y _ = ⊥-elim (x≢y (byteToNat-injective x≡y))
  ...   | tri> _ _ y<x = tri> (λ { (mk< x<y) → ℕ.<-asym x<y y<x }) x≢y (mk< y<x)

  <-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
  <-isStrictTotalOrder = record
    { isStrictPartialOrder = record
      { isEquivalence = isEquivalence
      ; irrefl        = <-irrefl
      ; trans         = <-trans
      ; <-resp-≈      = resp₂ _<_
      }
    ; compare = <-cmp
    }
```

## ByteStrings

ByteStrings are ordered lexicographically. For example,
`[0x23, 0x45, 0x67, 0x89] < [0x24]` and `[0x23, 0x45] < [0x23, 0x45, 0x00]`, and the
empty ByteString is smaller than every other ByteString.

`xs < ys` holds if `xs` is a proper prefix of `ys`, or if the first byte in which they
differ is smaller in `xs`.

```
infix 4 _<_

data _<_ : ByteString → ByteString → Set where
  []<∷  : ∀ {y ys}      → [] < y ∷ ys
  head< : ∀ {x y xs ys} → x Byte.< y → x ∷ xs < y ∷ ys
  tail< : ∀ {x xs ys}   → xs < ys → x ∷ xs < x ∷ ys

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (head< x<x)   = Byte.<-irrefl refl x<x
<-irrefl refl (tail< xs<xs) = <-irrefl refl xs<xs

<-trans : Transitive _<_
<-trans []<∷        (head< _)   = []<∷
<-trans []<∷        (tail< _)   = []<∷
<-trans (head< x<y) (head< y<z) = head< (Byte.<-trans x<y y<z)
<-trans (head< x<y) (tail< _)   = head< x<y
<-trans (tail< _)   (head< y<z) = head< y<z
<-trans (tail< p)   (tail< q)   = tail< (<-trans p q)

<-cmp : Trichotomous _≡_ _<_
<-cmp []       []       = tri≈ (λ ()) refl (λ ())
<-cmp []       (_ ∷ _)  = tri< []<∷ (λ ()) (λ ())
<-cmp (_ ∷ _)  []       = tri> (λ ()) (λ ()) []<∷
<-cmp (x ∷ xs) (y ∷ ys) with Byte.<-cmp x y
... | tri< x<y x≢y x≯y =
  tri< (head< x<y)
       (λ { refl → x≢y refl })
       (λ { (head< y<x) → x≯y y<x ; (tail< _) → x≢y refl })
... | tri> x≮y x≢y y<x =
  tri> (λ { (head< x<y) → x≮y x<y ; (tail< _) → x≢y refl })
       (λ { refl → x≢y refl })
       (head< y<x)
... | tri≈ _ refl _ with <-cmp xs ys
...   | tri< p ¬e ¬g =
  tri< (tail< p)
       (λ { refl → ¬e refl })
       (λ { (head< x<x) → Byte.<-irrefl refl x<x ; (tail< q) → ¬g q })
...   | tri≈ _ refl _ = tri≈ (<-irrefl refl) refl (<-irrefl refl)
...   | tri> ¬l ¬e g =
  tri> (λ { (head< x<x) → Byte.<-irrefl refl x<x ; (tail< q) → ¬l q })
       (λ { refl → ¬e refl })
       (tail< g)

<-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = resp₂ _<_
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  ; compare              = <-cmp
  }
```

## The non-strict order

`xs ≤ ys` holds if `xs < ys` or `xs ≡ ys`. We take `_≤_` from the standard
construction of a non-strict order from a strict one
(`Relation.Binary.Construct.StrictToNonStrict`), which also shows that it is a decidable
total order.

```
import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_ as NonStrict
open NonStrict public using (_≤_)

≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder = NonStrict.isDecTotalOrder <-isStrictTotalOrder
```

## Decision procedures

```
infix 4 _<?_ _≤?_

_<?_ : Decidable _<_
xs <? ys with <-cmp xs ys
... | tri< xs<ys _ _ = yes xs<ys
... | tri≈ xs≮ys _ _ = no xs≮ys
... | tri> xs≮ys _ _ = no xs≮ys

_≤?_ : Decidable _≤_
_≤?_ = NonStrict.decidable′ <-cmp

_<ᵇ_ : ByteString → ByteString → Bool
xs <ᵇ ys = does (xs <? ys)

_≤ᵇ_ : ByteString → ByteString → Bool
xs ≤ᵇ ys = does (xs ≤? ys)
```

Some tests:

```
private
  -- A byte literal; the bound is checked by computation.
  w : (n : ℕ.ℕ) → {T (n ℕ.<ᵇ 2 ℕ.^ 8)} → Binary.Byte
  w n {p} = natToByte n (ℕ.<ᵇ⇒< n (2 ℕ.^ 8) p)

  -- The first differing byte decides, regardless of later bytes.
  _ : (w 1 ∷ w 5 ∷ []) ≤ᵇ (w 2 ∷ w 0 ∷ []) ≡ true
  _ = refl

  _ : (w 2 ∷ w 0 ∷ []) ≤ᵇ (w 1 ∷ w 5 ∷ []) ≡ false
  _ = refl

  -- Equal prefixes defer to the rest.
  _ : (w 1 ∷ w 2 ∷ []) ≤ᵇ (w 1 ∷ w 3 ∷ []) ≡ true
  _ = refl

  _ : (w 1 ∷ w 3 ∷ []) ≤ᵇ (w 1 ∷ w 2 ∷ []) ≡ false
  _ = refl

  -- Reflexive, but not irreflexive.
  _ : (w 7 ∷ w 255 ∷ []) ≤ᵇ (w 7 ∷ w 255 ∷ []) ≡ true
  _ = refl

  _ : (w 7 ∷ w 255 ∷ []) <ᵇ (w 7 ∷ w 255 ∷ []) ≡ false
  _ = refl

  -- A proper prefix is smaller.
  _ : (w 1 ∷ []) <ᵇ (w 1 ∷ w 0 ∷ []) ≡ true
  _ = refl

  _ : (w 1 ∷ w 0 ∷ []) ≤ᵇ (w 1 ∷ []) ≡ false
  _ = refl

  _ : [] <ᵇ (w 0 ∷ []) ≡ true
  _ = refl

  _ : (w 0 ∷ []) ≤ᵇ [] ≡ false
  _ = refl
```
