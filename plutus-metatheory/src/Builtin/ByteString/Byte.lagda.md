---
title: Builtin.ByteString.Byte
layout: page
---

This module contains the formalisation of bytes, the elements of Plutus Core
bytestrings (see `Builtin.ByteString.Base`).

```
module Builtin.ByteString.Byte where
```

## Imports

```
open import Data.Bool using (Bool; true; false; _∧_; _∨_; _xor_; not; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Nat.Base using (⌊_/2⌋; parity)
open import Data.Parity.Base using (Parity; 0ℙ; 1ℙ)
open import Data.Integer using (ℤ; +_; -[1+_]; NonNegative)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec.Base using (Vec; _∷_; []; zipWith) renaming (map to vmap)
open import Relation.Nullary.Decidable using (does)
```

## The Byte type

A byte is eight bits, the first one being the most significant.

At runtime `Byte` is the Haskell mirror type in `FFI.ByteString`, so the
compiled bytestring builtins run the Agda implementations. Haskell bytestrings
are only used at the boundaries (postulated builtins, `DATA`, constants); see
`FFI.ByteString`.

```
data Byte : Set where
  byte : (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ : Bool) → Byte

{-# FOREIGN GHC import FFI.ByteString #-}
{-# COMPILE GHC Byte = data Byte (Byte) #-}

ᵇproj₁ : Byte → Bool
ᵇproj₂ : Byte → Bool
ᵇproj₃ : Byte → Bool
ᵇproj₄ : Byte → Bool
ᵇproj₅ : Byte → Bool
ᵇproj₆ : Byte → Bool
ᵇproj₇ : Byte → Bool
ᵇproj₈ : Byte → Bool
ᵇproj₁ (byte b₁ _ _ _ _ _ _ _) = b₁
ᵇproj₂ (byte _ b₂ _ _ _ _ _ _) = b₂
ᵇproj₃ (byte _ _ b₃ _ _ _ _ _) = b₃
ᵇproj₄ (byte _ _ _ b₄ _ _ _ _) = b₄
ᵇproj₅ (byte _ _ _ _ b₅ _ _ _) = b₅
ᵇproj₆ (byte _ _ _ _ _ b₆ _ _) = b₆
ᵇproj₇ (byte _ _ _ _ _ _ b₇ _) = b₇
ᵇproj₈ (byte _ _ _ _ _ _ _ b₈) = b₈

pattern 0B = byte false false false false false false false false

pattern 1B = byte false false false false false false false true

pattern 2B = byte false false false false false false true false

pattern 3B = byte false false false false false false true true

pattern 4B = byte false false false false false true false false

pattern 255B = byte true true true true true true true true

eqByte : Byte → Byte → Bool
eqByte (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) (byte c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) =
    does (b₁ ≟ c₁)
  ∧ does (b₂ ≟ c₂)
  ∧ does (b₃ ≟ c₃)
  ∧ does (b₄ ≟ c₄)
  ∧ does (b₅ ≟ c₅)
  ∧ does (b₆ ≟ c₆)
  ∧ does (b₇ ≟ c₇)
  ∧ does (b₈ ≟ c₈)
  where
    open import Data.Bool using (_≟_)
```

## Bits

`Bits n` is a vector of `n` bits, least significant first.

```
Bits : ℕ → Set
Bits n = Vec Bool n

byteToBits : Byte → Bits 8
byteToBits (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) =
  b₈ ∷ b₇ ∷ b₆ ∷ b₅ ∷ b₄ ∷ b₃ ∷ b₂ ∷ b₁ ∷ []

bitsToByte : Bits 8 → Byte
bitsToByte (b₈ ∷ b₇ ∷ b₆ ∷ b₅ ∷ b₄ ∷ b₃ ∷ b₂ ∷ b₁ ∷ []) =
  byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈

-- Using "ripple-carry addition" since implementing via suc/pred is not
-- structurally recursive and Agda can't prove termination.
-- The addition is modulo 256.
addBits : ∀ {n} → Bool → Bits n → Bits n → Bits n
addBits c [] [] = []
addBits c (x ∷ xs) (y ∷ ys) =
  (c xor (x xor y)) ∷ addBits ((x ∧ y) ∨ (c ∧ (x xor y))) xs ys

plusByte : Byte → Byte → Byte
plusByte x y = bitsToByte (addBits false (byteToBits x) (byteToBits y))

ℕToBits : (n : ℕ) → ℕ → Bits n
ℕToBits zero    _ = []
ℕToBits (suc n) k = lsb (parity k) ∷ ℕToBits n ⌊ k /2⌋
  where
    lsb : Parity → Bool
    lsb 0ℙ = false
    lsb 1ℙ = true

bitsToℕ : ∀ n → Bits n → ℕ
bitsToℕ zero _ = 0
bitsToℕ (suc n) (b ∷ xs) =
  (if b then 1 else 0) + 2 * bitsToℕ n xs
```

## Conversions to and from numbers

```
-- Conversion modulo 256
ℕToByte : ℕ → Byte
ℕToByte k = bitsToByte (ℕToBits 8 k)

byteToℕ : Byte → ℕ
byteToℕ b = bitsToℕ 8 (byteToBits b)

ℤToByte : (z : ℤ) .{{_ : NonNegative z}} → Byte
ℤToByte (+ n) = ℕToByte n

byteToℤ : Byte → ℤ
byteToℤ b = + (byteToℕ b)

-- conversion from an integer, which must lie in [0, 255].
toByte : ℤ → Maybe Byte
toByte (+ n)    = if n ≤ᵇ 255 then just (ℕToByte n) else nothing
toByte -[1+ _ ] = nothing
```

## Bitwise operations

```
andByte : Byte → Byte → Byte
andByte x y = bitsToByte (zipWith _∧_ (byteToBits x) (byteToBits y))

orByte : Byte → Byte → Byte
orByte x y = bitsToByte (zipWith _∨_ (byteToBits x) (byteToBits y))

xorByte : Byte → Byte → Byte
xorByte x y = bitsToByte (zipWith _xor_ (byteToBits x) (byteToBits y))

notByte : Byte → Byte
notByte x = bitsToByte (vmap not (byteToBits x))

popCount : Byte → ℕ
popCount b = count (byteToBits b)
  where
    count : ∀ {n} → Bits n → ℕ
    count [] = 0
    count (x ∷ xs) = (if x then 1 else 0) + count xs
```
