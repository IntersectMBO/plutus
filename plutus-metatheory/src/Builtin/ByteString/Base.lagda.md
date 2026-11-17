---
title: Builtin.ByteString.Base
layout: page
---

This module is a small ByteString library: the type of ByteStrings, list-like operations
on them, conversions to and from natural numbers and bit vectors, and the operations on
bits that the bitwise builtins are built from. Everything here is pure and total. The
semantics of the Cardano builtins, including the conditions under which they fail, is
given in `Builtin.ByteString` in terms of these definitions.

```
module Builtin.ByteString.Base where
```

## Imports

```
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; if_then_else_)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _^_; _<_; _%_)
open import Data.Nat.Properties using (<ᵇ⇒<; m∸n≤m; ≤-<-trans)
open import Data.Nat.DivMod using (m%n<n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function.Base using (_∘_)
open import Relation.Nullary using (Dec; yes; no)

import Data.Fin as Fin
import Data.Fin.Properties as Fin
import Data.List as L
import Data.Nat as ℕ
import Data.Vec as Vec
import Relation.Nullary.Decidable as Dec
import Builtin.Binary as Byte

open import Builtin.Binary
  using (Byte; Bits; bitVal; bitsToByte; byteToBits; byteToNat; natToByte;
         BinaryOf; binaryOf; binaryOfLen)
```

## ByteString

A ByteString is a finite sequence of bytes `[c₀, …, cₙ₋₁]`, also written `c₀⋯cₙ₋₁`. We
represent it as a list of bytes whose head is the leftmost byte `c₀`. The bytes of a
ByteString are indexed from the left, starting at 0, whereas its bits are indexed from the
right; the bit-level view below makes this precise.

```

infixr 5 _∷_

data ByteString : Set where
  []  : ByteString
  _∷_ : Byte → ByteString → ByteString
```

### Decidable Equality

```
_≟_ : (bs₁ bs₂ : ByteString) → Dec (bs₁ ≡ bs₂)
[] ≟ [] = yes refl
[] ≟ (_ ∷ _) = no λ()
(_ ∷ _) ≟ [] = no λ()
(x ∷ xs) ≟ (y ∷ ys) with x Byte.≟ y
... | yes refl = Dec.map′ (cong (x ∷_)) (λ { refl → refl }) (xs ≟ ys)
... | no x≢y   = no λ { refl → x≢y refl }
```

### Operations on ByteStrings

The usual list operations. `index i` returns the byte at the zero-based position `i`, and
`reverseAcc` is the accumulator-based helper behind `reverse`.

```
_++_ : ByteString → ByteString → ByteString
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : ByteString → ℕ
length []       = 0
length (_ ∷ xs) = 1 + length xs

take : ℕ → ByteString → ByteString
take zero    _        = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ℕ → ByteString → ByteString
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (_ ∷ xs) = drop n xs

index : ℕ → ByteString → Maybe Byte
index _       []       = nothing
index zero    (x ∷ _)  = just x
index (suc i) (_ ∷ xs) = index i xs

reverseAcc : ByteString → ByteString → ByteString
reverseAcc acc []       = acc
reverseAcc acc (x ∷ xs) = reverseAcc (x ∷ acc) xs

reverse : ByteString → ByteString
reverse = reverseAcc []

map : (Byte → Byte) → ByteString → ByteString
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

replicate : ℕ → Byte → ByteString
replicate zero    _ = []
replicate (suc n) b = b ∷ replicate n b
```

### Converting bits to ByteStrings

`padTo m bs` takes the first `m` bits of `bs`, padding with `false` (i.e. high zero bits,
since bits are little endian) when there are fewer than `m`.

```
padTo : (m : ℕ) → ∀ {k} → Bits k → Bits m
padTo zero    _        = []
padTo (suc m) []       = false ∷ padTo m []
padTo (suc m) (b ∷ bs) = b ∷ padTo m bs
```

Fold little-endian bits into a little-endian ByteString, 8 bits at a time. The first byte
holds the least significant bits; the last byte is padded with zeros if `len` is not a
multiple of 8.

```
bitsToByteStringLE : ∀ {len} → Bits len → ByteString
bitsToByteStringLE [] = []
bitsToByteStringLE (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ bs) =
  bitsToByte (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ []) ∷ bitsToByteStringLE bs
bitsToByteStringLE bs = bitsToByte (padTo 8 bs) ∷ []
  -- ^ fewer than 8 bits left
```

### Natural Numbers as ByteStrings

A natural number `n` is represented by its base-256 expansion
`n = a₀ + 256a₁ + 256²a₂ + ⋯`. In little-endian (LE) order the least significant byte `a₀`
comes first; in big-endian (BE) order it comes last.

`natToByteStringLE` and `natToByteStringBE` use as few bytes as possible, and a single
byte for 0. The `Len` variants use exactly `w` bytes, padding with `0x00` bytes on the
right in the little-endian case and on the left in the big-endian case. For example, the
five-byte little-endian representation of `0x123456` is `[0x56, 0x34, 0x12, 0x00, 0x00]`
and its five-byte big-endian representation is `[0x00, 0x00, 0x12, 0x34, 0x56]`. The bound
on `n` guarantees that it fits.

Conversely, `byteStringToNatLE` and `byteStringToNatBE` compute
`c₀ + 256c₁ + ⋯ + 256ⁿ⁻¹cₙ₋₁` and `256ⁿ⁻¹c₀ + ⋯ + 256cₙ₋₂ + cₙ₋₁` respectively, for a
ByteString `[c₀, …, cₙ₋₁]`.

```
natToByteStringLE : (n : ℕ) → .(n < 2 ^ 65536) → ByteString
natToByteStringLE n _ = bitsToByteStringLE (BinaryOf.bits (binaryOf n))

natToByteStringLenLE : (w n : ℕ) → .(n < 2 ^ (8 * w)) → ByteString
natToByteStringLenLE w n n< =
  bitsToByteStringLE (BinaryOf.bits (binaryOfLen (8 * w) n n<))

natToByteStringBE : (n : ℕ) → .(n < 2 ^ 65536) → ByteString
natToByteStringBE n p = reverse (natToByteStringLE n p)

natToByteStringLenBE : (w n : ℕ) → .(n < 2 ^ (8 * w)) → ByteString
natToByteStringLenBE w n p = reverse (natToByteStringLenLE w n p)

byteStringToNatLE : ByteString → ℕ
byteStringToNatLE []       = 0
byteStringToNatLE (b ∷ bs) = byteToNat b + 256 * byteStringToNatLE bs

byteStringToNatBE : ByteString → ℕ
byteStringToNatBE = byteStringToNatLE ∘ reverse
```

### Bit-level View

A ByteString of `n` bytes can also be viewed as a bitstring `b₈ₙ₋₁ ⋯ b₀` of `8n` bits, by
writing out the bits of each byte, most significant first, and concatenating them.
Formally, the ByteString `[c₀, …, cₙ₋₁]` and the bitstring `b₈ₙ₋₁ ⋯ b₀` correspond when
`cⱼ = b₈ₖ + 2b₈ₖ₊₁ + ⋯ + 128b₈ₖ₊₇`, where `k = n - 1 - j`, for every `j`. So bit `0` is
the least significant bit of the *last* byte, and bit `8n - 1` the most significant bit of
the first byte.

`toBits` computes this view, storing the bits from `b₀` upwards so that position `i` of
the vector holds `bᵢ`, and `fromBits` is its inverse. `toVec` and `fromVec` convert
between ByteStrings and vectors of bytes.

```
toVec : (bs : ByteString) → Vec Byte (length bs)
toVec []       = []
toVec (b ∷ bs) = b ∷ toVec bs

fromVec : ∀ {n} → Vec Byte n → ByteString
fromVec []       = []
fromVec (b ∷ bs) = b ∷ fromVec bs

toBits : (bs : ByteString) → Bits (length bs * 8)
toBits bs = Vec.concat (Vec.map byteToBits (Vec.reverse (toVec bs)))

groupBytes : ∀ n → Bits (n * 8) → Vec Byte n
groupBytes zero    []                                    = []
groupBytes (suc n) (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ bs) =
  bitsToByte (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ []) ∷ groupBytes n bs

fromBits : ∀ n → Bits (n * 8) → ByteString
fromBits n bs = fromVec (Vec.reverse (groupBytes n bs))
```

`onBits f` applies a length-preserving operation `f` on bits to a ByteString, by going
through its bit-level view.

```
onBits : (∀ {n} → Bits n → Bits n) → ByteString → ByteString
onBits f bs = fromBits (length bs) (f (toBits bs))
```

### Operations on Bits

The operations below are defined index by index: for a bit vector of length `n`, `bᵢ` is
bit `i` of the input and `dᵢ` is bit `i` of the result.

Shifting by an integer `k` moves every bit `k` places towards the most significant end, or
`-k` places towards the least significant end if `k` is negative, and fills vacated
positions with 𝟶: `dᵢ = bᵢ₋ₖ` if `0 ≤ i - k ≤ n - 1`, and `dᵢ = 𝟶` otherwise.

`shiftLeft k` is the shift by `k`, and `shiftRight k` the shift by `-k`, so that
`dᵢ = bᵢ₊ₖ`. `shiftRightAt` computes a single bit of a right shift; it is exported so that
its properties can be proved.

```
shiftLeft : ∀ {n} → ℕ → Bits n → Bits n
shiftLeft k bs = Vec.tabulate λ i →
  if k ℕ.≤ᵇ Fin.toℕ i
    then
      Vec.lookup
        bs
        (Fin.fromℕ<
          (≤-<-trans (m∸n≤m (Fin.toℕ i) k) (Fin.toℕ<n i))
        )
    else false

shiftRightAt : ∀ {n} → ℕ → Bits n → Fin n → Bool
shiftRightAt {n} k bs i with Fin.toℕ i + k ℕ.<? n
... | yes p = Vec.lookup bs (Fin.fromℕ< p)
... | no _  = false

shiftRight : ∀ {n} → ℕ → Bits n → Bits n
shiftRight k bs = Vec.tabulate (shiftRightAt k bs)
```

Rotating by an integer `k` is like shifting, except that bits moving past one end re-enter
at the other: `dᵢ = b₍ᵢ₋ₖ₎ mod n`, where `x mod n` is the least non-negative remainder.

`rotateRight m` is the rotation by `-m`, with `dᵢ = b₍ᵢ₊ₘ₎ mod n`. `rotateLeft k` is the
rotation by `k`, which is the same as a right rotation by `n ∸ k % n`.

```
rotateRight : ∀ {n} → ℕ → Bits n → Bits n
rotateRight {zero}      _ bs = bs
rotateRight {n@(suc _)} m bs =
  Vec.tabulate λ i →
    Vec.lookup bs (Fin.fromℕ< (m%n<n (Fin.toℕ i + m) n))

rotateLeft : ∀ {n} → ℕ → Bits n → Bits n
rotateLeft {zero}      _ bs = bs
rotateLeft {n@(suc _)} k bs = rotateRight (n ∸ k % n) bs
```

Counting, searching and writing bits:

* `popCount` counts the bits that are 𝟷, that is, the size of `{i : bᵢ = 𝟷}`.
* `findFirstSet` returns the index of the lowest bit that is 𝟷, `min {i : bᵢ = 𝟷}`, or
  `nothing` if every bit is 𝟶.
* `setBits is u` sets each bit whose index occurs in `is` to `u`, and leaves the others
  unchanged. Indices may be repeated.

```
popCount : ∀ {n} → Bits n → ℕ
popCount []       = 0
popCount (b ∷ bs) = bitVal b + popCount bs

findFirstSet : ∀ {n} → Bits n → Maybe (Fin n)
findFirstSet []           = nothing
findFirstSet (true  ∷ _)  = just Fin.zero
findFirstSet (false ∷ bs) with findFirstSet bs
... | just i  = just (Fin.suc i)
... | nothing = nothing

setBits : ∀ {n} → L.List (Fin n) → Bool → Bits n → Bits n
setBits is u bs = L.foldr (λ i acc → acc Vec.[ i ]≔ u) bs is
```

The logical operations combine two ByteStrings bit by bit. When the inputs have different
lengths, they are first brought to the same length, either by truncating the longer one on
the right or by extending the shorter one on the right with copies of a padding bit. Since
this removes or adds whole bytes at the end, `zipWithExtend` combines its inputs byte by
byte, aligned at their first byte. If `extend` is `false` the result is as long as the
shorter input; if it is `true`, the shorter input is extended with `padByte` to the length
of the longer one.

```
zipWithExtend
  : (Byte → Byte → Byte) → (extend : Bool) → (padByte : Byte)
  → ByteString → ByteString → ByteString
zipWithExtend f e     p []       []       = []
zipWithExtend f e     p (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithExtend f e p xs ys
zipWithExtend f false p []       (_ ∷ _)  = []
zipWithExtend f false p (_ ∷ _)  []       = []
zipWithExtend f true  p []       (y ∷ ys) = f p y ∷ zipWithExtend f true p [] ys
zipWithExtend f true  p (x ∷ xs) []       = f x p ∷ zipWithExtend f true p xs []
```

### Ordering

ByteStrings are ordered lexicographically. For `a = [a₁, …, aₘ]` and `b = [b₁, …, bₙ]`,
`a ≤ b` if and only if

* `a = []`, or
* `m, n > 0` and `a₁ < b₁`, or
* `m, n > 0`, `a₁ = b₁` and `[a₂, …, aₘ] ≤ [b₂, …, bₙ]`.

For example, `[0x23, 0x45, 0x67, 0x89] < [0x24]` and `[0x23, 0x45] < [0x23, 0x45, 0x00]`,
and the empty ByteString is below every other ByteString.

```
_≤ᵇ_ : ByteString → ByteString → Bool
[] ≤ᵇ _ = true
_ ≤ᵇ [] = false
(b₁ ∷ bs₁) ≤ᵇ (b₂ ∷ bs₂) =
  (byteToNat b₁ ℕ.<ᵇ byteToNat b₂)
  ∨ ((byteToNat b₁ ℕ.≡ᵇ byteToNat b₂) ∧ (bs₁ ≤ᵇ bs₂))
```

Some tests:

```
private
  -- A byte literal; the bound is checked by computation.
  w : (n : ℕ) → {T (n ℕ.<ᵇ 2 ^ 8)} → Byte
  w n {p} = natToByte n (<ᵇ⇒< n (2 ^ 8) p)

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

  -- Reflexive.
  _ : (w 7 ∷ w 255 ∷ []) ≤ᵇ (w 7 ∷ w 255 ∷ []) ≡ true
  _ = refl

  -- A proper prefix is smaller.
  _ : (w 1 ∷ []) ≤ᵇ (w 1 ∷ w 0 ∷ []) ≡ true
  _ = refl

  _ : (w 1 ∷ w 0 ∷ []) ≤ᵇ (w 1 ∷ []) ≡ false
  _ = refl

  _ : [] ≤ᵇ (w 0 ∷ []) ≡ true
  _ = refl

  _ : (w 0 ∷ []) ≤ᵇ [] ≡ false
  _ = refl

  -- byteStringToNat: endianness, leading zeros, empty input.
  _ : byteStringToNatLE (w 1 ∷ w 2 ∷ []) ≡ 513
  _ = refl

  _ : byteStringToNatBE (w 1 ∷ w 2 ∷ []) ≡ 258
  _ = refl

  _ : byteStringToNatBE (w 0 ∷ w 0 ∷ w 7 ∷ []) ≡ 7
  _ = refl

  _ : byteStringToNatLE (w 7 ∷ w 0 ∷ []) ≡ 7
  _ = refl

  _ : byteStringToNatBE [] ≡ 0
  _ = refl

```