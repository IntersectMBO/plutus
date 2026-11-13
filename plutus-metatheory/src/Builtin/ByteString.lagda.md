---
title: Builtin.ByteString
layout: page
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module Builtin.ByteString where
```

## Imports

```
open import Builtin.ByteString.Base
open import Builtin.ByteString.Byte hiding (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer using (ℤ; +_)
open import Data.Nat using (ℕ; _^_)
open import Relation.Nullary.Decidable using (yes; no; does)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Function.Base using (_∘_; _$_)
open import Utils using (List)

import Data.Nat.Properties as ℕ
import Data.Integer as ℤ
import Builtin.Integer.Base as ℤ
```

## Cardano Builtin Functions on ByteString

### Batch 1

```
appendByteString : ByteString → ByteString → ByteString
appendByteString = _++_

consByteStringV2 : ℤ → ByteString → Maybe ByteString
consByteStringV2 (ℤ.pos n) bs with n ℕ.<? 2 ^ 8
... | yes p = just (natToByte n p ∷ bs)
... | no _ = nothing
consByteStringV2 (ℤ.negsuc n) _ = nothing

sliceByteString : ℤ → ℤ → ByteString → ByteString
sliceByteString start subStrLen bs =
  take (clamp subStrLen) (drop (clamp start) bs)
  where
    clamp : ℤ → ℕ
    clamp (ℤ.pos n)    = n
    clamp (ℤ.negsuc _) = 0

lengthOfByteString : ByteString → ℤ
lengthOfByteString = (+_) ∘ length

indexByteString : ℤ → ByteString → Maybe Byte
indexByteString (ℤ.pos i)    bs = index i bs
indexByteString (ℤ.negsuc _) _  = nothing

equalsByteString : ByteString → ByteString → Bool
equalsByteString bs₁ bs₂ = does (bs₁ ≟ bs₂)

lessThanByteString : ByteString → ByteString → Bool
lessThanByteString bs₁ bs₂ = (bs₁ ≤ᵇ bs₂) ∧ (not (equalsByteString bs₁ bs₂))

lessThanEqualsByteString : ByteString → ByteString → Bool
lessThanEqualsByteString bs₁ bs₂ = bs₁ ≤ᵇ bs₂

```

### Batch 4

```
integerToByteString : Bool → ℤ → ℤ → Maybe ByteString
integerToByteString = {!   !}

byteStringToInteger : Bool → ByteString → ℤ
byteStringToInteger = {!   !}
```

### Batch 5

```
andByteString : Bool → ByteString → ByteString → ByteString
andByteString = {!   !}

orByteString : Bool → ByteString → ByteString → ByteString
orByteString = {!   !}

xorByteString : Bool → ByteString → ByteString → ByteString
xorByteString = {!   !}

complementByteString : ByteString → ByteString
complementByteString = {!   !}

shiftByteString : ByteString → ℤ → ByteString
shiftByteString = {!   !}

rotateByteString : ByteString → ℤ → ByteString
rotateByteString = {!   !}

countSetBits : ByteString → ℤ
countSetBits = {!   !}

findFirstSetBit : ByteString → ℤ
findFirstSetBit = {!   !}

readBit : ByteString → ℤ → Maybe Bool
readBit = {!   !}

writeBits : ByteString → List ℤ → Bool → Maybe ByteString
writeBits = {!   !}

replicateByte : ℤ → ℤ → Maybe ByteString
replicateByte = {!   !}
```