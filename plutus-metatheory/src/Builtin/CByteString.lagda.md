---
title: Builtin.CByteString
layout: page
---

```
module Builtin.CByteString where
```

This module contains the formalisation of Cardano ByteStrings: ByteStrings of at most
65536 bytes. It plays the same role for ByteStrings as `Builtin.CInteger` does for
integers.

In the builtin semantics followed by the metatheory, most ByteString builtins require
their ByteString arguments to be at most `maxLength` bytes long, and fail otherwise. Only
the arguments are bounded: a builtin may return a longer ByteString, for example
`appendByteString` applied to two ByteStrings of `maxLength` bytes.

## Imports

```
open import Data.Bool using (Bool; false)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary.Decidable using (yes; no)

import Data.Maybe as Maybe
import Data.Nat.Properties as ℕ

open import Builtin.Binary using (Byte; fillByte)
open import Builtin.ByteString.Base using (ByteString; []; _∷_; length; replicate)
import Builtin.ByteString as BS
```

## The CByteString type

A `CByteString` is a ByteString together with a proof that its length is at most
`maxLength`.

```
maxLength : ℕ
maxLength = 65536

data CByteString : Set where
  cBS
    : (bs : ByteString)
    → .(length bs ≤ maxLength)
    → CByteString

toByteString : CByteString → ByteString
toByteString (cBS bs _) = bs
```

`mkCByteString` checks the bound. This is where a builtin fails when one of its
arguments is too long.

```
mkCByteString : ByteString → Maybe CByteString
mkCByteString bs with length bs ℕ.≤? maxLength
... | yes p = just (cBS bs p)
... | no _ = nothing
```

## CByteString operations

Each builtin forgets the bound and calls the definition in `Builtin.ByteString`.

```
appendByteString : CByteString → CByteString → ByteString
appendByteString (cBS bs₁ _) (cBS bs₂ _) = BS.appendByteString bs₁ bs₂

consByteStringV2 : ℤ → CByteString → Maybe ByteString
consByteStringV2 c (cBS bs _) = BS.consByteStringV2 c bs

sliceByteString : ℤ → ℤ → CByteString → Maybe ByteString
sliceByteString start len (cBS bs _) = BS.sliceByteString start len bs

indexByteString : CByteString → ℤ → Maybe Byte
indexByteString (cBS bs _) = BS.indexByteString bs

equalsByteString : CByteString → CByteString → Bool
equalsByteString (cBS bs₁ _) (cBS bs₂ _) = BS.equalsByteString bs₁ bs₂

lessThanByteString : CByteString → CByteString → Bool
lessThanByteString (cBS bs₁ _) (cBS bs₂ _) = BS.lessThanByteString bs₁ bs₂

lessThanEqualsByteString : CByteString → CByteString → Bool
lessThanEqualsByteString (cBS bs₁ _) (cBS bs₂ _) =
  BS.lessThanEqualsByteString bs₁ bs₂

byteStringToInteger : Bool → CByteString → ℤ
byteStringToInteger e (cBS bs _) = BS.byteStringToInteger e bs

andByteString : Bool → CByteString → CByteString → ByteString
andByteString e (cBS bs₁ _) (cBS bs₂ _) = BS.andByteString e bs₁ bs₂

orByteString : Bool → CByteString → CByteString → ByteString
orByteString e (cBS bs₁ _) (cBS bs₂ _) = BS.orByteString e bs₁ bs₂

xorByteString : Bool → CByteString → CByteString → ByteString
xorByteString e (cBS bs₁ _) (cBS bs₂ _) = BS.xorByteString e bs₁ bs₂

complementByteString : CByteString → ByteString
complementByteString (cBS bs _) = BS.complementByteString bs

readBit : CByteString → ℤ → Maybe Bool
readBit (cBS bs _) = BS.readBit bs

countSetBits : CByteString → ℤ
countSetBits (cBS bs _) = BS.countSetBits bs

findFirstSetBit : CByteString → ℤ
findFirstSetBit (cBS bs _) = BS.findFirstSetBit bs
```

## Properties

`mkCByteString` succeeds exactly on the ByteStrings of at most `maxLength` bytes, and
it keeps the ByteString unchanged.

```
mkCByteString-sound
  : ∀ {bs c} → mkCByteString bs ≡ just c → toByteString c ≡ bs
mkCByteString-sound {bs = bs} _ with length bs ℕ.≤? maxLength
mkCByteString-sound refl | yes _ = refl
mkCByteString-sound ()   | no _

mkCByteString-complete
  : ∀ bs → length bs ≤ maxLength → ∃[ c ] mkCByteString bs ≡ just c
mkCByteString-complete bs bs≤max with length bs ℕ.≤? maxLength
... | yes p      = cBS bs p , refl
... | no  bs≰max = ⊥-elim (bs≰max bs≤max)

mkCByteString-nothing
  : ∀ bs → maxLength < length bs → mkCByteString bs ≡ nothing
mkCByteString-nothing bs max<bs with length bs ℕ.≤? maxLength
... | yes bs≤max = ⊥-elim (ℕ.<⇒≱ max<bs bs≤max)
... | no  _      = refl
```

## Tests

Testing the boundary by `refl` would make Agda normalise ByteStrings of 65536 bytes, so
the boundary is tested through the lemmas above instead. The lemma `length-replicate` is
needed for this.

```
length-replicate : ∀ n b → length (replicate n b) ≡ n
length-replicate zero    _ = refl
length-replicate (suc n) b = cong suc (length-replicate n b)

private
  zero⁸ : Byte
  zero⁸ = fillByte false

  -- The empty ByteString is a valid argument.
  _ : Maybe.map toByteString (mkCByteString []) ≡ just []
  _ = refl

  -- A ByteString of exactly `maxLength` bytes is a valid argument...
  _ : ∃[ c ] mkCByteString (replicate maxLength zero⁸) ≡ just c
  _ = mkCByteString-complete (replicate maxLength zero⁸)
        (ℕ.≤-reflexive (length-replicate maxLength zero⁸))

  -- ... but one more byte is too many.
  _ : mkCByteString (replicate (suc maxLength) zero⁸) ≡ nothing
  _ = mkCByteString-nothing (replicate (suc maxLength) zero⁸)
        (ℕ.≤-reflexive (sym (length-replicate (suc maxLength) zero⁸)))
```
