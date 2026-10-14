---
title: Builtin.ByteString.Denotation
layout: page
---

This module contains the denotations of the bytestring builtins (except the
hashes, encoding and serialisation, which are postulated in `Builtin`). They
are used by the CEK machines, and at runtime the compiled code runs these
definitions.

```
module Builtin.ByteString.Denotation where
```

## Imports

```
open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.Nat as ℕ using ()
open import Data.Integer using (ℤ; +_; -[1+_]; 0ℤ; 1ℤ; _+_; _*_; _≤ᵇ_; ∣_∣; _≤?_; _<?_; _≟_; nonNegative)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.List using (List; foldr)
open import Data.Bool.ListAction using (all)
open import Relation.Nullary.Decidable using (does; yes; no)

open import Builtin.ByteString.Byte
open import Builtin.ByteString.Base
```

## Basic operations

```
lengthBS : ByteString → ℤ
lengthBS [] = + 0
lengthBS (_ ∷ xs) = (+ 1) + lengthBS xs

concat : ByteString → ByteString → ByteString
concat [] ys = ys
concat (x ∷ xs) ys = x ∷ concat xs ys

equals : ByteString → ByteString → Bool
equals = eqByteString

-- Lexicographic order on bytestrings, comparing bytes as unsigned numbers.
B<= : ByteString → ByteString → Bool
B<= [] _ = true
B<= (_ ∷ _) [] = false
B<= (b₁ ∷ tail₁) (b₂ ∷ tail₂) =
  if byteToℕ b₁ ℕ.<ᵇ byteToℕ b₂ then true
  else if byteToℕ b₁ ℕ.≡ᵇ byteToℕ b₂ then B<= tail₁ tail₂
  else false

B< : ByteString → ByteString → Bool
B< bs₁ bs₂ = B<= bs₁ bs₂ ∧ not (equals bs₁ bs₂)

-- The argument must be a valid byte value, i.e. in [0, 255]; otherwise the
-- builtin fails.
cons : ℤ → ByteString → Maybe ByteString
cons i xs with (+ 0) ≤? i
... | yes p =
        if i ≤ᵇ (+ 255) then just (ℤToByte i ∷ xs) else nothing
    where
      instance _ = nonNegative p
... | no _ = nothing

slice : ℤ → ℤ → ByteString → ByteString
slice s k bs = take k (dropB s bs)

-- Look up the byte at index ix, where the first byte has index n.
indexFrom : ℤ → ℤ → ByteString → Maybe Byte
indexFrom ix _ [] = nothing
indexFrom ix n (x ∷ xs) =
  if does (n ≟ ix)
  then just x
  else indexFrom ix (n + 1ℤ) xs

index : ByteString → ℤ → Maybe ℤ
index bs ix = map byteToℤ (indexFrom ix 0ℤ bs)
```

## Bitwise operations and integer conversions (CIP-121, CIP-122, CIP-123)

```
-- The number of bits in a bytestring.
bitLength : ByteString → ℤ
bitLength bs = lengthBS bs * (+ 8)

-- Is i a valid bit index for a bytestring with n bits?
validBitIndex : ℤ → ℤ → Bool
validBitIndex n i = (0ℤ ≤ᵇ i) ∧ does (i <? n)

-- The production implementation takes the shift/rotation amount as a 64-bit
-- Haskell `Int`, so amounts outside its range fail; we reproduce that here.
fitsInt : ℤ → Bool
fitsInt i = (-[1+ 9223372036854775807 ] ≤ᵇ i) ∧ (i ≤ᵇ + 9223372036854775807)

BStoI : Bool → ByteString → ℤ
BStoI true  bs = + byteStringToℕ bs
BStoI false bs = + byteStringToℕ (reverseBS bs)

ItoBS : Bool → ℤ → ℤ → Maybe ByteString
ItoBS e w n =
  if (0ℤ ≤ᵇ w) ∧ (w ≤ᵇ + 8192) ∧ (0ℤ ≤ᵇ n)
  then ℕToByteString e ∣ w ∣ ∣ n ∣
  else nothing

andBYTESTRING : Bool → ByteString → ByteString → ByteString
andBYTESTRING pad = zipWithBS andByte pad 255B

orBYTESTRING : Bool → ByteString → ByteString → ByteString
orBYTESTRING pad = zipWithBS orByte pad 0B

xorBYTESTRING : Bool → ByteString → ByteString → ByteString
xorBYTESTRING pad = zipWithBS xorByte pad 0B

complementBYTESTRING : ByteString → ByteString
complementBYTESTRING = mapBS notByte

readBIT : ByteString → ℤ → Maybe Bool
readBIT bs i =
  if validBitIndex (bitLength bs) i
  then lookupBit (toBits bs) ∣ i ∣
  else nothing

writeBITS : ByteString → List ℤ → Bool → Maybe ByteString
writeBITS bs ixs u =
  if all (validBitIndex (bitLength bs)) ixs
  then just (fromBits (foldr (λ i → setBit ∣ i ∣ u) (toBits bs) ixs))
  else nothing

replicateBYTE : ℤ → ℤ → Maybe ByteString
replicateBYTE l w with toByte w
... | nothing = nothing
... | just b  =
  if (0ℤ ≤ᵇ l) ∧ (l ≤ᵇ + 8192)
  then just (replicateBS ∣ l ∣ b)
  else nothing

shiftBYTESTRING : ByteString → ℤ → Maybe ByteString
shiftBYTESTRING bs k =
  if fitsInt k
  then just (fromBits (shiftBits k (toBits bs)))
  else nothing

rotateBYTESTRING : ByteString → ℤ → Maybe ByteString
rotateBYTESTRING bs k =
  if fitsInt k
  then just (fromBits (rotateBits k (toBits bs)))
  else nothing

countSetBITS : ByteString → ℤ
countSetBITS []       = 0ℤ
countSetBITS (b ∷ bs) = (+ popCount b) + countSetBITS bs

findFirstSetBIT : ByteString → ℤ
findFirstSetBIT bs = firstSetBit (toBits bs)
```
