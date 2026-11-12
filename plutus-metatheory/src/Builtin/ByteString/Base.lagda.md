---
title: Builtin.ByteString.Base
layout: page
---

```
module Builtin.ByteString.Base where
```

## Imports

```
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _/_; _%_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (*-comm)
open import Data.Nat.DivMod using (m<n*o⇒m/o<n; m%n<n; m≡m%n+[m/n]*n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Function.Base using (_∘_; _$_)
import Data.Fin as Fin
import Data.Fin.Properties as Fin
import Data.Vec as Vec
import Data.Nat as ℕ
```

## Bits

```
Bits : ℕ → Set
Bits n = Vec Bool n

```

### Base 2 numerals

For a natural number `n`, `BinaryOf n` is a representation of `n` in binary notation.

If the `len` is greater than the minimum required to represent `n`, the `Bits` vector is padded
with `false` bits. 

The bits are in little endian order.

Design decision: instead of using intrinsic types like `Fin` to build the representation of
binary numerals, we prefer to use refinement types since they are computationally cheaper.

```
bitVal : Bool → ℕ
bitVal false = 0
bitVal true  = 1

bitsToNat : ∀ {n} → Bits n → ℕ
bitsToNat []       = 0
bitsToNat (b ∷ bs) = bitVal b + 2 * bitsToNat bs

record BinaryOf (n : ℕ) : Set where
  constructor binary
  field
    len      : ℕ
    bits     : Bits len
    .correct : bitsToNat bits ≡ n
    -- ^ The proof is irrelevant because we don't want it to be evaluated at neither
    -- Agda compile-time nor Agda runtime.

natToBits : (len : ℕ) → ℕ → Bits len
natToBits zero      _ = []
natToBits (suc len) k = (k % 2 ≡ᵇ 1) ∷ natToBits len (k / 2)

```

## Byte

```
data Byte : Set where
  byte : (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ : Bool) → Byte

bitsToByte : Bits 8 → Byte
bitsToByte (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ x₈ ∷ []) = 
  byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈

natToByte : (n : ℕ) → .(n < 2 ^ 8) → Byte
natToByte n _ = bitsToByte (natToBits 8 n)

```

## ByteString

```

infixr 5 _∷_

data ByteString : Set where
  []  : ByteString
  _∷_ : Byte → ByteString → ByteString
```

### Operations on ByteStrings

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

```