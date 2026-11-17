---
title: Builtin.ByteString
layout: page
---

```
module Builtin.ByteString where
```

## Imports

```
open import Builtin.ByteString.Base
open import Builtin.Binary hiding (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer using (ℤ; +_)
open import Data.Nat using (ℕ; suc; _*_; _^_; _<ᵇ_)
open import Relation.Nullary.Decidable using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; true; false; not; T; _∧_; _∨_; _xor_; if_then_else_)
open import Function.Base using (_∘_; _$_)
open import Utils using (List; []; _∷_; toList; mapM; MaybeMonad; intToFin)

import Data.Fin as Fin
import Data.Maybe as Maybe
import Data.Vec as Vec
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
integerToByteString endianness (ℤ.pos 0) (ℤ.pos n) with n ℕ.<? 2 ^ 65536
... | no _ = nothing
... | yes p = just $
  if endianness
    then natToByteStringBE n p
    else natToByteStringLE n p
integerToByteString endianness (ℤ.pos w) (ℤ.pos n)
  with w ℕ.≤? 8192 | n ℕ.<? 2 ^ (8 * w)
... | yes _ | yes p = just $
  if endianness
    then natToByteStringLenBE w n p
    else natToByteStringLenLE w n p
... | _     | _     = nothing
integerToByteString _ _ _   = nothing

byteStringToInteger : Bool → ByteString → ℤ
byteStringToInteger endianness bs =
  + (if endianness then byteStringToNatBE bs else byteStringToNatLE bs)
```

### Batch 5

```
andByteString : Bool → ByteString → ByteString → ByteString
andByteString extend = zipWithExtend (zipWithByte _∧_) extend (fillByte true)

orByteString : Bool → ByteString → ByteString → ByteString
orByteString extend = zipWithExtend (zipWithByte _∨_) extend (fillByte false)

xorByteString : Bool → ByteString → ByteString → ByteString
xorByteString extend = zipWithExtend (zipWithByte _xor_) extend (fillByte false)

complementByteString : ByteString → ByteString
complementByteString = map (mapByte not)
```

Shifts and rotations: a positive amount moves bits towards higher indices (to the left, in
the specification's notation), a negative one towards lower indices.

```
shiftByteString : ByteString → ℤ → ByteString
shiftByteString bs (ℤ.pos k)    = onBits (shiftLeft k) bs
shiftByteString bs (ℤ.negsuc k) = onBits (shiftRight (suc k)) bs

rotateByteString : ByteString → ℤ → ByteString
rotateByteString bs (ℤ.pos k)    = onBits (rotateLeft k) bs
rotateByteString bs (ℤ.negsuc k) = onBits (rotateRight (suc k)) bs

countSetBits : ByteString → ℤ
countSetBits bs = + popCount (toBits bs)

findFirstSetBit : ByteString → ℤ
findFirstSetBit bs with findFirstSet (toBits bs)
... | just i  = + Fin.toℕ i
... | nothing = ℤ.-[1+ 0 ]
```

Bit indices arrive as integers; they are valid if they are in `[0, n)`.

```
readBit : ByteString → ℤ → Maybe Bool
readBit bs j = Maybe.map (Vec.lookup (toBits bs)) (intToFin j)
```

`writeBits` fails if any index is out of bounds.

```
writeBits : ByteString → List ℤ → Bool → Maybe ByteString
writeBits bs js u =
  Maybe.map (λ is → fromBits (length bs) (setBits (toList is) u (toBits bs)))
            (mapM intToFin js)

replicateByte : ℤ → ℤ → Maybe ByteString
replicateByte (ℤ.pos l) (ℤ.pos b) with l ℕ.≤? 8192 | b ℕ.<? 2 ^ 8
... | yes _ | yes p = just (replicate l (natToByte b p))
... | _     | _     = nothing
replicateByte _ _ = nothing
```

Some tests, including the examples from CIP-122 and CIP-123:

```
private
  -- A byte literal; the bound is checked by computation.
  w : (n : ℕ) → {T (n <ᵇ 2 ^ 8)} → Byte
  w n {p} = natToByte n (ℕ.<ᵇ⇒< n (2 ^ 8) p)

  bsEBFC : ByteString
  bsEBFC = w 0xEB ∷ w 0xFC ∷ []

  -- Logical operations: truncation vs. extension.
  _ : andByteString false (w 0xF0 ∷ w 0xFF ∷ []) (w 0x0F ∷ []) ≡ w 0x00 ∷ []
  _ = refl

  _ : andByteString true (w 0xF0 ∷ w 0xFF ∷ []) (w 0x0F ∷ []) ≡ w 0x00 ∷ w 0xFF ∷ []
  _ = refl

  _ : orByteString true (w 0x0F ∷ []) (w 0xF0 ∷ w 0x12 ∷ []) ≡ w 0xFF ∷ w 0x12 ∷ []
  _ = refl

  _ : xorByteString false (w 0xFF ∷ w 0x12 ∷ []) (w 0x0F ∷ []) ≡ w 0xF0 ∷ []
  _ = refl

  _ : complementByteString (w 0xF0 ∷ w 0x00 ∷ []) ≡ w 0x0F ∷ w 0xFF ∷ []
  _ = refl

  -- Shifts.
  _ : shiftByteString bsEBFC (+ 5) ≡ w 0x7F ∷ w 0x80 ∷ []
  _ = refl

  _ : shiftByteString bsEBFC ℤ.-[1+ 4 ] ≡ w 0x07 ∷ w 0x5F ∷ []
  _ = refl

  _ : shiftByteString bsEBFC (+ 16) ≡ w 0x00 ∷ w 0x00 ∷ []
  _ = refl

  _ : shiftByteString bsEBFC (+ 0) ≡ bsEBFC
  _ = refl

  -- Rotations.
  _ : rotateByteString bsEBFC (+ 5) ≡ w 0x7F ∷ w 0x9D ∷ []
  _ = refl

  _ : rotateByteString bsEBFC ℤ.-[1+ 4 ] ≡ w 0xE7 ∷ w 0x5F ∷ []
  _ = refl

  _ : rotateByteString bsEBFC (+ 21) ≡ w 0x7F ∷ w 0x9D ∷ []
  _ = refl

  _ : rotateByteString bsEBFC (+ 16) ≡ bsEBFC
  _ = refl

  -- Counting and searching.
  _ : countSetBits bsEBFC ≡ + 12
  _ = refl

  _ : findFirstSetBit bsEBFC ≡ + 2
  _ = refl

  _ : findFirstSetBit (w 0x00 ∷ w 0x00 ∷ []) ≡ ℤ.-[1+ 0 ]
  _ = refl

  -- Reading and writing bits; bit 0 is in the last byte.
  _ : readBit bsEBFC (+ 2) ≡ just true
  _ = refl

  _ : readBit bsEBFC (+ 15) ≡ just true
  _ = refl

  _ : readBit bsEBFC (+ 16) ≡ nothing
  _ = refl

  _ : writeBits (w 0x00 ∷ w 0x00 ∷ []) (+ 0 ∷ + 15 ∷ []) true
    ≡ just (w 0x80 ∷ w 0x01 ∷ [])
  _ = refl

  _ : writeBits bsEBFC (+ 2 ∷ + 16 ∷ []) false ≡ nothing
  _ = refl

  -- Replicating bytes.
  _ : replicateByte (+ 2) (+ 255) ≡ just (w 0xFF ∷ w 0xFF ∷ [])
  _ = refl

  _ : replicateByte (+ 2) (+ 256) ≡ nothing
  _ = refl
```
