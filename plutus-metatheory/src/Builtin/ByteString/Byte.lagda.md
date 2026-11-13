---
title: Builtin.ByteString.Byte
layout: page
---

```
module Builtin.ByteString.Byte where
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
open import Function.Base using (_∘_; _$_; _$′_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Fin as Fin
import Data.Fin.Properties as Fin
import Data.Vec as Vec
import Data.Vec.Properties as Vec
import Data.Nat as ℕ
import Data.Bool as 𝔹
import Relation.Nullary.Decidable as Dec
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
record Byte : Set where
  constructor byte
  field
    b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ : Bool

bitsToByte : Bits 8 → Byte
bitsToByte (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ x₈ ∷ []) = 
  byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈

byteToBits : Byte → Bits 8
byteToBits (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) =
  b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ []

natToByte : (n : ℕ) → .(n < 2 ^ 8) → Byte
natToByte n _ = bitsToByte $′ natToBits 8 n

byteToNat : Byte → ℕ
byteToNat = bitsToNat ∘ byteToBits

```


### Decidable Equality

```
_≟_ : (b₁ b₂ : Byte) → Dec (b₁ ≡ b₂)
b₁ ≟ b₂ =
  Dec.map′
    (cong bitsToByte {byteToBits b₁} {byteToBits b₂})
    (cong byteToBits)
    (Vec.≡-dec 𝔹._≟_ (byteToBits b₁) (byteToBits b₂))
```