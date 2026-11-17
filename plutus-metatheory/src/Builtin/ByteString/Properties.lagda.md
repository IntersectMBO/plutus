---
title: Builtin.ByteString.Properties
layout: page
---

```
module Builtin.ByteString.Properties where
```

## Imports

```
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (+-assoc; *-assoc; *-distribˡ-+; +-identityʳ; ≤ᵇ⇒≤)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (recompute)

import Data.Nat as ℕ
import Data.Vec as Vec

open import Builtin.Binary
  using (Bits; bitVal; bitsToNat; bitsToByte; byteToNat; byteToBits-bitsToByte;
         BinaryOf; binary; binaryOf; binaryOfLen)
open import Builtin.ByteString.Base
  using (ByteString; []; _∷_; _++_; reverseAcc; reverse; padTo; bitsToByteStringLE;
         natToByteStringLE; natToByteStringBE; natToByteStringLenLE; natToByteStringLenBE;
         byteStringToNatLE; byteStringToNatBE)
```

## Concatenation and Reversal

```
++-identityʳ : ∀ xs → xs ++ [] ≡ xs
++-identityʳ []       = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

++-assoc : ∀ xs ys zs → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

reverseAcc-++ : ∀ acc xs → reverseAcc acc xs ≡ reverse xs ++ acc
reverseAcc-++ acc []       = refl
reverseAcc-++ acc (x ∷ xs) =
  trans (reverseAcc-++ (x ∷ acc) xs)
        (sym (trans (cong (_++ acc) (reverseAcc-++ (x ∷ []) xs))
                    (++-assoc (reverse xs) (x ∷ []) acc)))

private
  reverse-reverseAcc : ∀ acc xs → reverse (reverseAcc acc xs) ≡ reverse acc ++ xs
  reverse-reverseAcc acc []       = sym (++-identityʳ (reverse acc))
  reverse-reverseAcc acc (x ∷ xs) =
    trans (reverse-reverseAcc (x ∷ acc) xs)
          (trans (cong (_++ xs) (reverseAcc-++ (x ∷ []) acc))
                 (++-assoc (reverse acc) (x ∷ []) xs))

reverse-involutive : ∀ xs → reverse (reverse xs) ≡ xs
reverse-involutive = reverse-reverseAcc []
```

## Bits

`bitsToNat` of a concatenation: the bits of the second part are shifted by the length of
the first.

```
bitsToNat-++
  : ∀ {m n} (xs : Bits m) (ys : Bits n)
  → bitsToNat (xs Vec.++ ys) ≡ bitsToNat xs + 2 ^ m * bitsToNat ys
bitsToNat-++ []       ys = sym (+-identityʳ (bitsToNat ys))
bitsToNat-++ {suc m} (x ∷ xs) ys = begin
  bitVal x + 2 * bitsToNat (xs Vec.++ ys)
    ≡⟨ cong (λ r → bitVal x + 2 * r) (bitsToNat-++ xs ys) ⟩
  bitVal x + 2 * (a + p * y)
    ≡⟨ cong (bitVal x +_) (*-distribˡ-+ 2 a (p * y)) ⟩
  bitVal x + (2 * a + 2 * (p * y))
    ≡⟨ sym (+-assoc (bitVal x) (2 * a) (2 * (p * y))) ⟩
  bitVal x + 2 * a + 2 * (p * y)
    ≡⟨ cong (bitVal x + 2 * a +_) (sym (*-assoc 2 p y)) ⟩
  bitVal x + 2 * a + 2 * p * y
    ∎
  where
    open ≡-Reasoning
    a = bitsToNat xs
    p = 2 ^ m
    y = bitsToNat ys
```

Padding with high zero bits does not change the value.

```
bitsToNat-padTo : ∀ m {k} (bs : Bits k) → k ≤ m → bitsToNat (padTo m bs) ≡ bitsToNat bs
bitsToNat-padTo zero    []       _         = refl
bitsToNat-padTo (suc m) []       _         = cong (2 *_) (bitsToNat-padTo m [] z≤n)
bitsToNat-padTo (suc m) (b ∷ bs) (s≤s k≤m) =
  cong (λ r → bitVal b + 2 * r) (bitsToNat-padTo m bs k≤m)
```

The bits of a `BinaryOf n` denote `n`. The `correct` field is irrelevant, so we recompute
it from decidable equality (matching on the constructor, as irrelevant projections are
unsafe).

```
bitsToNat-bits : ∀ {n} (x : BinaryOf n) → bitsToNat (BinaryOf.bits x) ≡ n
bitsToNat-bits (binary _ bs p) = recompute (bitsToNat bs ℕ.≟ _) p
```

## Bits to ByteString and back

Reading back the little-endian ByteString built from some bits yields the number those bits
denote, including when the last byte is padded.

```
private
  -- The final, padded byte (fewer than 8 bits left).
  lastByte
    : ∀ {k} (bs : Bits k) → k ≤ 8
    → byteToNat (bitsToByte (padTo 8 bs)) + 256 * 0 ≡ bitsToNat bs
  lastByte bs k≤8 =
    trans (+-identityʳ _)
          (trans (cong bitsToNat (byteToBits-bitsToByte (padTo 8 bs)))
                 (bitsToNat-padTo 8 bs k≤8))

byteStringToNatLE-bitsToByteStringLE
  : ∀ {len} (bs : Bits len) → byteStringToNatLE (bitsToByteStringLE bs) ≡ bitsToNat bs
byteStringToNatLE-bitsToByteStringLE [] = refl
byteStringToNatLE-bitsToByteStringLE (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ bs) =
  trans (cong (λ r → byteToNat (bitsToByte byte) + 256 * r)
              (byteStringToNatLE-bitsToByteStringLE bs))
        (sym (bitsToNat-++ byte bs))
  where byte = b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ []
byteStringToNatLE-bitsToByteStringLE bs@(_ ∷ []) =
  lastByte bs (≤ᵇ⇒≤ _ 8 _)
byteStringToNatLE-bitsToByteStringLE bs@(_ ∷ _ ∷ []) =
  lastByte bs (≤ᵇ⇒≤ _ 8 _)
byteStringToNatLE-bitsToByteStringLE bs@(_ ∷ _ ∷ _ ∷ []) =
  lastByte bs (≤ᵇ⇒≤ _ 8 _)
byteStringToNatLE-bitsToByteStringLE bs@(_ ∷ _ ∷ _ ∷ _ ∷ []) =
  lastByte bs (≤ᵇ⇒≤ _ 8 _)
byteStringToNatLE-bitsToByteStringLE bs@(_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) =
  lastByte bs (≤ᵇ⇒≤ _ 8 _)
byteStringToNatLE-bitsToByteStringLE bs@(_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) =
  lastByte bs (≤ᵇ⇒≤ _ 8 _)
byteStringToNatLE-bitsToByteStringLE bs@(_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) =
  lastByte bs (≤ᵇ⇒≤ _ 8 _)
```

## Round Trips: Natural Number → ByteString → Natural Number

Minimal-width encoding:

```
byteStringToNatLE-natToByteStringLE
  : ∀ n .(p : n < 2 ^ 65536) → byteStringToNatLE (natToByteStringLE n p) ≡ n
byteStringToNatLE-natToByteStringLE n _ =
  trans (byteStringToNatLE-bitsToByteStringLE (BinaryOf.bits (binaryOf n)))
        (bitsToNat-bits (binaryOf n))

byteStringToNatBE-natToByteStringBE
  : ∀ n .(p : n < 2 ^ 65536) → byteStringToNatBE (natToByteStringBE n p) ≡ n
byteStringToNatBE-natToByteStringBE n p =
  trans (cong byteStringToNatLE (reverse-involutive (natToByteStringLE n p)))
        (byteStringToNatLE-natToByteStringLE n p)
```

Fixed-width encoding, `w` bytes:

```
byteStringToNatLE-natToByteStringLenLE
  : ∀ w n .(p : n < 2 ^ (8 * w)) → byteStringToNatLE (natToByteStringLenLE w n p) ≡ n
byteStringToNatLE-natToByteStringLenLE w n p =
  trans (byteStringToNatLE-bitsToByteStringLE (BinaryOf.bits (binaryOfLen (8 * w) n p)))
        (bitsToNat-bits (binaryOfLen (8 * w) n p))

byteStringToNatBE-natToByteStringLenBE
  : ∀ w n .(p : n < 2 ^ (8 * w)) → byteStringToNatBE (natToByteStringLenBE w n p) ≡ n
byteStringToNatBE-natToByteStringLenBE w n p =
  trans (cong byteStringToNatLE (reverse-involutive (natToByteStringLenLE w n p)))
        (byteStringToNatLE-natToByteStringLenLE w n p)
```
