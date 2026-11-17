---
title: Builtin.ByteString
layout: page
---

```
module Builtin.ByteString where
```

This module defines the semantics of the Cardano builtin functions on ByteStrings. It only
exports the builtins. They are defined in terms of the pure ByteString library in
`Builtin.ByteString.Base`; this module adds the handling of integer arguments, and the
bounds and failure conditions of each builtin.

## Imports

```
open import Builtin.ByteString.Base
open import Builtin.Binary hiding (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer using (ℤ; +_)
open import Data.Nat using (ℕ; suc; _*_; _∸_; _^_; _<ᵇ_)
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

The builtins are grouped by the batch that introduced them. A builtin that can fail
returns a `Maybe`, where `nothing` signals an error; the others are total.

### Batch 1

`appendByteString` concatenates two ByteStrings: `[c₁, …, cₘ]` and `[d₁, …, dₙ]` give
`[c₁, …, cₘ, d₁, …, dₙ]`.

```
appendByteString : ByteString → ByteString → ByteString
appendByteString = _++_
```

`consByteString c s` prepends the byte `c` to `s`. It requires `0 ≤ c ≤ 255`, and fails
otherwise. An earlier semantics variant of this builtin instead reduces `c` modulo 256 and
never fails; only the current variant is defined here.

```
consByteStringV2 : ℤ → ByteString → Maybe ByteString
consByteStringV2 (ℤ.pos n) bs with n ℕ.<? 2 ^ 8
... | yes p = just (natToByte n p ∷ bs)
... | no _ = nothing
consByteStringV2 (ℤ.negsuc n) _ = nothing
```

`sliceByteString s k b` returns the substring of `b` of length `k` starting at the
zero-based position `s`. It does not fail when the arguments are out of range: negative
arguments are treated as zero, and the substring stops at the end of `b`. That is, for
`b = [c₀, …, cₙ₋₁]` the result is `[cᵢ, …, cⱼ₋₁]` where `i = min(max(s, 0), n)` and
`j = min(i + max(k, 0), n)`. For example, slicing `"TheCakeIsALie"` from position `-3`
with length `5` gives `"TheCa"`.

Both arguments must, however, fit in a signed 64-bit integer, that is, lie in
`[-2⁶³, 2⁶³ - 1]`; otherwise the builtin fails. `fitsInt` checks this range.

```
private
  fitsInt : ℤ → Bool
  fitsInt (ℤ.pos n)    = n <ᵇ 2 ^ 63
  fitsInt (ℤ.negsuc n) = n <ᵇ 2 ^ 63

sliceByteString : ℤ → ℤ → ByteString → Maybe ByteString
sliceByteString start subStrLen bs =
  if fitsInt start ∧ fitsInt subStrLen
    then just (take (clamp subStrLen) (drop (clamp start) bs))
    else nothing
  where
    clamp : ℤ → ℕ
    clamp (ℤ.pos n)    = n
    clamp (ℤ.negsuc _) = 0
```

`lengthOfByteString` returns the number of bytes in a ByteString. `indexByteString s i`
returns the byte at the zero-based position `i` of `s`, and fails unless
`0 ≤ i < length s`.

```
lengthOfByteString : ByteString → ℤ
lengthOfByteString = (+_) ∘ length

indexByteString : ByteString → ℤ → Maybe Byte
indexByteString bs (ℤ.pos i)    = index i bs
indexByteString _  (ℤ.negsuc _) = nothing
```

`equalsByteString` decides equality: two ByteStrings are equal if and only if they have
the same length and the same byte at every position. `lessThanEqualsByteString` is the
lexicographic order `_≤ᵇ_` defined in `Builtin.ByteString.Base`, and `lessThanByteString`
is its strict version: `a < b` if and only if `a ≤ b` and `a ≠ b`.

```
equalsByteString : ByteString → ByteString → Bool
equalsByteString bs₁ bs₂ = does (bs₁ ≟ bs₂)

lessThanByteString : ByteString → ByteString → Bool
lessThanByteString bs₁ bs₂ = (bs₁ ≤ᵇ bs₂) ∧ (not (equalsByteString bs₁ bs₂))

lessThanEqualsByteString : ByteString → ByteString → Bool
lessThanEqualsByteString bs₁ bs₂ = bs₁ ≤ᵇ bs₂
```

### Batch 4

Conversions between non-negative integers and ByteStrings. The first argument of each
builtin selects the byte order: big-endian if it is `true`, and little-endian if it is
`false`.

`integerToByteString e w n` converts the integer `n` to a ByteString of width `w`. It
requires `0 ≤ w ≤ 8192` and `0 ≤ n < 256⁸¹⁹² = 2⁶⁵⁵³⁶`, and fails otherwise; in particular
it fails on negative inputs.

* If `w = 0`, the result is as short as possible: the base-256 digits of `n`, without
  leading zero bytes. In particular `0` is converted to the empty ByteString.
* If `w > 0`, the result is exactly `w` bytes long, padded with `0x00` bytes on the right
  in little-endian order and on the left in big-endian order. The builtin fails if `n`
  does not fit in `w` bytes, that is, if `n ≥ 2⁸ʷ`. In particular `0` is converted to `w`
  zero bytes.

For example, the five-byte little-endian representation of `0x123456` is
`[0x56, 0x34, 0x12, 0x00, 0x00]`, and its five-byte big-endian representation is
`[0x00, 0x00, 0x12, 0x34, 0x56]`. When `w > 0`, the check `n < 2 ^ (8 * w)` also implies
the bound `n < 2 ^ 65536`.

```
integerToByteString : Bool → ℤ → ℤ → Maybe ByteString
integerToByteString _          (ℤ.pos 0) (ℤ.pos 0) = just []
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
```

`byteStringToInteger e s` converts a ByteString to a non-negative integer. For
`s = [c₀, …, cₙ₋₁]` the result is `c₀ + 256c₁ + ⋯ + 256ⁿ⁻¹cₙ₋₁` in little-endian
order, and `256ⁿ⁻¹c₀ + ⋯ + 256cₙ₋₂ + cₙ₋₁` in big-endian order. Every ByteString is a
valid input, whatever its length, and the empty ByteString is converted to `0`.

```
byteStringToInteger : Bool → ByteString → ℤ
byteStringToInteger endianness bs =
  + (if endianness then byteStringToNatBE bs else byteStringToNatLE bs)
```

### Batch 5

Logical and bitwise operations on ByteStrings. Most of them work on the bit-level view of
a ByteString defined in `Builtin.ByteString.Base`, in which a ByteString of `n` bytes is
the bitstring `b₈ₙ₋₁ ⋯ b₀`, and bit `0` is the least significant bit of the last byte.

`andByteString`, `orByteString` and `xorByteString` extend the bitwise operations ∧, ∨ and
⊕ to ByteStrings. When the inputs have different lengths, the first argument decides what
happens. If it is `false`, the longer input is truncated on the right to the length of the
shorter one. If it is `true`, the shorter input is extended on the right to the length of
the longer one, with 𝟷 bits for `andByteString` and 𝟶 bits for `orByteString` and
`xorByteString`, so that the extra bytes of the longer input are copied unchanged.
`complementByteString` flips every bit.

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

`shiftByteString s k` shifts the bits of `s` by `|k|` places: towards the most significant
end if `k ≥ 0`, and towards the least significant end if `k < 0`. Vacated positions are
filled with 𝟶, so shifting by at least the length of `s` in bits clears every bit.
`rotateByteString s k` rotates the bits instead: bits moving past one end re-enter at the
other. Both preserve the length of `s`.

`countSetBits s` is the number of bits of `s` that are 𝟷. `findFirstSetBit s` is the index
of the lowest bit of `s` that is 𝟷, and `-1` if all bits are 𝟶.

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

`readBit s i` returns the bit `bᵢ` of `s`, and fails unless `0 ≤ i < 8 * length s`.
`writeBits s J u` sets every bit of `s` whose index occurs in the list `J` to `u` (𝟷 for
`true`, 𝟶 for `false`), and leaves the other bits unchanged. `J` may contain repetitions,
and the builtin fails if any index in `J` is out of bounds. Integer indices are converted
with `intToFin`, which fails on out-of-range values.

```
readBit : ByteString → ℤ → Maybe Bool
readBit bs j = Maybe.map (Vec.lookup (toBits bs)) (intToFin j)

writeBits : ByteString → List ℤ → Bool → Maybe ByteString
writeBits bs js u =
  Maybe.map (λ is → fromBits (length bs) (setBits (toList is) u (toBits bs)))
            (mapM intToFin js)
```

`replicateByte l B` returns the ByteString of length `l` whose bytes are all `B`. It fails
unless `0 ≤ l ≤ 8192` and `0 ≤ B ≤ 255`.

```
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

  -- Slicing: negative arguments count as zero, out-of-`Int` ones fail.
  _ : sliceByteString ℤ.-[1+ 2 ] (+ 2) bsEBFC ≡ just bsEBFC
  _ = refl

  _ : sliceByteString (+ 1) (+ (2 ^ 63)) bsEBFC ≡ nothing
  _ = refl

  _ : sliceByteString (+ 1) (+ (2 ^ 63 ∸ 1)) bsEBFC ≡ just (w 0xFC ∷ [])
  _ = refl

  -- Indexing takes the ByteString first.
  _ : indexByteString bsEBFC (+ 1) ≡ just (w 0xFC)
  _ = refl

  -- Zero is encoded in exactly `w` bytes.
  _ : integerToByteString true (+ 0) (+ 0) ≡ just []
  _ = refl

  _ : integerToByteString false (+ 2) (+ 0) ≡ just (w 0x00 ∷ w 0x00 ∷ [])
  _ = refl

  -- Replicating bytes.
  _ : replicateByte (+ 2) (+ 255) ≡ just (w 0xFF ∷ w 0xFF ∷ [])
  _ = refl

  _ : replicateByte (+ 2) (+ 256) ≡ nothing
  _ = refl
```
