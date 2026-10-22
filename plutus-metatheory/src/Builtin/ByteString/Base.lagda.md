---
title: Builtin.ByteString.Base
layout: page
---

This module contains the formalisation of Plutus Core bytestrings, and the
operations on them used to define the bytestring builtins (see
`Builtin.ByteString.Denotation`).

```
module Builtin.ByteString.Base where
```

## Imports

```
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _≤ᵇ_)
open import Data.Integer as I using (ℤ; +_; -[1+_])
import Data.List as L
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing; maybe) renaming (_>>=_ to mbind)
open import Data.Vec.Base using (_∷_; []) renaming (toList to vecToList)
open import Function.Base using (case_of_)

open import Builtin.ByteString.Byte
```

## The ByteString type

At runtime `ByteString` is the Haskell mirror type in `FFI.ByteString` (see
`Builtin.ByteString.Byte`).

```
data ByteString : Set where
  []  : ByteString
  _∷_ : Byte → ByteString → ByteString

{-# FOREIGN GHC import FFI.ByteString #-}
{-# COMPILE GHC ByteString = data ByteString (BSNil | BSCons) #-}

eqByteString : ByteString → ByteString → Bool
eqByteString [] [] = true
eqByteString (x ∷ xs) (y ∷ ys) = eqByte x y ∧ eqByteString xs ys
eqByteString _ _ = false
```

## Literals

Bytestring literals, written in hexadecimal as in the textual syntax of UPLC
(two digits per byte, most significant first, either case). This is what
`FFI.AgdaUnparse` emits for bytestring constants, and it reduces at
type-checking time. `fromHex` fails on malformed input (a non-hex character or
an odd number of digits), and `mkByteString` then gives the empty bytestring.

```
fromHex : String → Maybe ByteString
fromHex s = go (Data.String.toList s)
  where
    open import Data.Char using (Char) renaming (toℕ to charToℕ)

    hexDigit : Char → Maybe ℕ
    hexDigit c with charToℕ c
    ... | n = if (48 ≤ᵇ n) ∧ (n ≤ᵇ 57)  then just (n ∸ 48)
         else if (65 ≤ᵇ n) ∧ (n ≤ᵇ 70)  then just (n ∸ 55)
         else if (97 ≤ᵇ n) ∧ (n ≤ᵇ 102) then just (n ∸ 87)
         else nothing

    go : L.List Char → Maybe ByteString
    go L.[] = just []
    go (hi L.∷ lo L.∷ cs) =
      mbind (hexDigit hi) λ h →
      mbind (hexDigit lo) λ l →
      mbind (go cs) λ bs →
      just (ℕToByte (16 * h + l) ∷ bs)
    go (_ L.∷ L.[]) = nothing

mkByteString : String → ByteString
mkByteString s = maybe (λ bs → bs) [] (fromHex s)
```

## List operations

```
lengthℕ : ByteString → ℕ
lengthℕ []       = 0
lengthℕ (_ ∷ xs) = suc (lengthℕ xs)

take : ℤ → ByteString → ByteString
take z bs =
  if z I.≤ᵇ I.0ℤ
  then []
  else
    case bs of λ {
        [] → []
      ; (x ∷ xs) → x ∷ take (z I.- I.1ℤ) xs
      }

dropB : ℤ → ByteString → ByteString
dropB z bs =
  if z I.≤ᵇ I.0ℤ
  then bs
  else
    case bs of λ {
        [] → []
      ; (_ ∷ xs) → dropB (z I.- I.1ℤ) xs
      }

replicateBS : ℕ → Byte → ByteString
replicateBS zero    _ = []
replicateBS (suc n) b = b ∷ replicateBS n b

_++ᵇ_ : ByteString → ByteString → ByteString
[]       ++ᵇ ys = ys
(x ∷ xs) ++ᵇ ys = x ∷ (xs ++ᵇ ys)

reverseAcc : ByteString → ByteString → ByteString
reverseAcc acc []       = acc
reverseAcc acc (x ∷ xs) = reverseAcc (x ∷ acc) xs

reverseBS : ByteString → ByteString
reverseBS = reverseAcc []

mapBS : (Byte → Byte) → ByteString → ByteString
mapBS f []       = []
mapBS f (x ∷ xs) = f x ∷ mapBS f xs

-- Combine two bytestrings byte by byte. If they have different lengths then,
-- depending on `pad`, either the longer one is truncated on the right or the
-- shorter one is extended on the right with `padByte`.
zipWithBS : (Byte → Byte → Byte) → (pad : Bool) → (padByte : Byte)
          → ByteString → ByteString → ByteString
zipWithBS f pad padByte []       []       = []
zipWithBS f pad padByte []       (y ∷ ys) = if pad then f padByte y ∷ zipWithBS f pad padByte [] ys else []
zipWithBS f pad padByte (x ∷ xs) []       = if pad then f x padByte ∷ zipWithBS f pad padByte xs [] else []
zipWithBS f pad padByte (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithBS f pad padByte xs ys
```

## Bitstring representation of bytestrings

Bit indexing follows CIP-122: bit 0 is the least significant bit of the last
byte and bit 8n-1 is the most significant bit of the first byte. The functions
below convert between a bytestring and the list of its bits in index order,
i.e. the element at position i of `toBits bs` is bit i of `bs`.

```
Bits* : Set
Bits* = L.List Bool

toBitsAcc : Bits* → ByteString → Bits*
toBitsAcc acc []       = acc
toBitsAcc acc (x ∷ xs) = toBitsAcc (vecToList (byteToBits x) L.++ acc) xs

toBits : ByteString → Bits*
toBits = toBitsAcc L.[]

-- Inverse of `toBits`. The input is consumed eight bits at a time; a trailing
-- incomplete byte is dropped.
fromBitsAcc : ByteString → Bits* → ByteString
fromBitsAcc acc (b₀ L.∷ b₁ L.∷ b₂ L.∷ b₃ L.∷ b₄ L.∷ b₅ L.∷ b₆ L.∷ b₇ L.∷ rest) =
  fromBitsAcc (bitsToByte (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) ∷ acc) rest
fromBitsAcc acc _ = acc

fromBits : Bits* → ByteString
fromBits = fromBitsAcc []

lookupBit : Bits* → ℕ → Maybe Bool
lookupBit L.[]       _       = nothing
lookupBit (b L.∷ bs) zero    = just b
lookupBit (b L.∷ bs) (suc i) = lookupBit bs i

setBit : ℕ → Bool → Bits* → Bits*
setBit _       _ L.[]       = L.[]
setBit zero    u (b L.∷ bs) = u L.∷ bs
setBit (suc i) u (b L.∷ bs) = b L.∷ setBit i u bs

-- Index of the first set bit, counting from the given offset, or -1 if there
-- is none.
firstSetBitFrom : ℕ → Bits* → ℤ
firstSetBitFrom i L.[]           = -[1+ 0 ]
firstSetBitFrom i (true  L.∷ _)  = + i
firstSetBitFrom i (false L.∷ bs) = firstSetBitFrom (suc i) bs

-- Index of the first set bit, or -1 if there is none.
firstSetBit : Bits* → ℤ
firstSetBit = firstSetBitFrom 0

-- Shift the bits k places to the left (k ≥ 0) or right (k < 0), filling the
-- vacated positions with 0 and keeping the length unchanged.
shiftBits : ℤ → Bits* → Bits*
shiftBits k bits =
  if n ≤ᵇ I.∣ k ∣
  then L.replicate n false
  else shifted k
  where
    n : ℕ
    n = L.length bits
    shifted : ℤ → Bits*
    shifted (+ k)    = L.replicate k false L.++ L.take (n ∸ k) bits
    shifted -[1+ k ] = L.drop (suc k) bits L.++ L.replicate (suc k) false

-- Rotate the bits k places to the left (k ≥ 0) or right (k < 0).
rotateBits : ℤ → Bits* → Bits*
rotateBits k L.[]             = L.[]
rotateBits k bits@(_ L.∷ _)   = L.drop (n ∸ r) bits L.++ L.take (n ∸ r) bits
  where
    open import Data.Integer.DivMod using (_%ℕ_)
    n : ℕ
    n = L.length bits
    r : ℕ
    r = k %ℕ n
```

## Conversion between bytestrings and natural numbers

```
-- Big-endian interpretation of a bytestring.
byteStringToℕAcc : ℕ → ByteString → ℕ
byteStringToℕAcc acc []       = acc
byteStringToℕAcc acc (b ∷ bs) = byteStringToℕAcc (acc * 256 + byteToℕ b) bs

byteStringToℕ : ByteString → ℕ
byteStringToℕ = byteStringToℕAcc 0

-- Base-256 digits of a natural number, least significant first. The first
-- argument bounds the number of digits; `nothing` is returned if it is
-- exceeded. (The bound makes the recursion structural.)
digits256 : ℕ → ℕ → Maybe ByteString
digits256 _          zero    = just []
digits256 zero       (suc _) = nothing
digits256 (suc fuel) (suc k) =
  Data.Maybe.map (ℕToByte (suc k % 256) ∷_) (digits256 fuel (suc k / 256))
  where open import Data.Nat.Base using (_%_; _/_)

-- Big-endian (if the flag is true) or little-endian encoding of a natural
-- number as a bytestring of width w (or of minimal width if w = 0), as
-- specified for the `integerToByteString` builtin. The result is `nothing` if
-- the number does not fit in w bytes, or if it needs more than 8192 bytes.
ℕToByteString : Bool → ℕ → ℕ → Maybe ByteString
ℕToByteString e w zero    = just (replicateBS w 0B)
ℕToByteString e w (suc n) with digits256 8192 (suc n)
... | nothing = nothing
... | just ds =
  if (w == 0) ∨ (lengthℕ ds ≤ᵇ w)
  then just (if e then replicateBS (w ∸ lengthℕ ds) 0B ++ᵇ reverseBS ds
                  else ds ++ᵇ replicateBS (w ∸ lengthℕ ds) 0B)
  else nothing
  where open import Agda.Builtin.Nat using (_==_)
```
