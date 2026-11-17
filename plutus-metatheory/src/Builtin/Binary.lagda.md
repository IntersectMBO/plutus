---
title: Builtin.Binary
layout: page
---

This module defines bits, bytes and binary representations of natural numbers. They
underpin the ByteString library in `Builtin.ByteString.Base`, and with it the conversions
between integers and ByteStrings performed by the Cardano builtins.

Bytes are the natural numbers from 0 to 255, and bits are 𝟶 and 𝟷. Every byte `c` can be
written uniquely as `c = b₀ + 2b₁ + 4b₂ + ⋯ + 128b₇` with bits `b₀, …, b₇`. We take this
decomposition as the definition: a `Byte` consists of eight bits, and its numeric value is
computed from them.

```
module Builtin.Binary where
```

## Imports

```
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; _/_; _%_; _≡ᵇ_; z≤n; s≤s; s≤s⁻¹; ⌊_/2⌋)
open import Data.Nat.DivMod
  using (m<n*o⇒m/o<n; m%n<n; m≡m%n+[m/n]*n; m*n%n≡0; [m+kn]%n≡m%n; m*n/n≡m; +-distrib-/)
open import Data.Nat.Properties
  using (*-comm; ≤-refl; ≤-trans; ≤-reflexive; +-suc; *-monoʳ-≤; ⌊n/2⌋<n)
open import Data.Nat.Logarithm using (⌊log₂_⌋)
open import Data.Nat.Logarithm.Core using (⌊log2⌋)
open import Induction.WellFounded using (Acc; acc)
open import Data.Vec using (Vec; []; _∷_)
open import Function.Base using (_∘_; _$′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (recompute)

import Data.Bool as 𝔹
import Data.Vec.Properties as Vec
import Relation.Nullary.Decidable as Dec
```

## Bits

A bit is a boolean: `true` stands for 𝟷 and `false` for 𝟶. `Bits n` is a vector of `n`
bits. Bit vectors are little endian: position `i` holds the bit `bᵢ`, of weight `2ⁱ`. When
writing a bitstring we put the most significant bit on the left, as in `bₙ₋₁ ⋯ b₀`, so a
vector stores the bits in the reverse of their written order.

```
Bits : ℕ → Set
Bits n = Vec Bool n
```

## Representing Natural Numbers in Binary

`bitsToNat` computes the value `b₀ + 2b₁ + ⋯ + 2ⁿ⁻¹bₙ₋₁` of a little-endian bit vector.
Its inverse, `natToBits len n`, produces exactly `len` bits: it pads with `false` bits
when `len` is larger than the minimum required to represent `n`, and truncates when it is
smaller. For this reason, it is private and one should use the smart constructors
`binaryOf` and `binaryOfLen` instead.

```
bitVal : Bool → ℕ
bitVal false = 0
bitVal true  = 1

bitsToNat : ∀ {n} → Bits n → ℕ
bitsToNat []       = 0
bitsToNat (b ∷ bs) = bitVal b + 2 * bitsToNat bs

private
  natToBits : (len : ℕ) → ℕ → Bits len
  natToBits zero      _ = []
  natToBits (suc len) k = (k % 2 ≡ᵇ 1) ∷ natToBits len (k / 2)
```

For a natural number `n`, `BinaryOf n` is a representation of `n` in binary notation.

Design decision: instead of using intrinsic types like `Fin` to build the representation of
binary numerals, we prefer to use refinement types since they are computationally cheaper.

```
record BinaryOf (n : ℕ) : Set where
  constructor binary
  field
    len      : ℕ
    bits     : Bits len
    .correct : bitsToNat bits ≡ n
    -- ^ The proof is irrelevant because we don't want it to be evaluated at
    -- Agda compile-time or Agda runtime.
```

## Byte

A byte is a record of eight bits, from the least significant `b₁` to the most significant
`b₈`, so that its value is `b₁ + 2b₂ + ⋯ + 128b₈`. Representing bytes by their bits,
rather than as numbers below 256, makes the bit-level operations needed by the bitwise
builtins structural. `natToByte` and `byteToNat` convert between bytes and the numbers
from 0 to 255.

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

Bitwise operations on bytes act on each of the eight bits independently. They are the
building blocks of the logical builtins: `fillByte b` is the byte whose bits are all `b`
(that is, `0xFF` or `0x00`), `mapByte f` applies `f` to every bit (as in
`complementByteString`), and `zipWithByte f` combines corresponding bits of two bytes (as
in `andByteString`, `orByteString` and `xorByteString`).

```
fillByte : Bool → Byte
fillByte b = byte b b b b b b b b

mapByte : (Bool → Bool) → Byte → Byte
mapByte f (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) =
  byte (f b₁) (f b₂) (f b₃) (f b₄) (f b₅) (f b₆) (f b₇) (f b₈)

zipWithByte : (Bool → Bool → Bool) → Byte → Byte → Byte
zipWithByte f (byte a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) =
  byte (f a₁ b₁) (f a₂ b₂) (f a₃ b₃) (f a₄ b₄) (f a₅ b₅) (f a₆ b₆) (f a₇ b₇) (f a₈ b₈)
```

### Decidable Equality for Byte

```
_≟_ : (b₁ b₂ : Byte) → Dec (b₁ ≡ b₂)
b₁ ≟ b₂ =
  Dec.map′
    (cong bitsToByte {byteToBits b₁} {byteToBits b₂})
    (cong byteToBits)
    (Vec.≡-dec 𝔹._≟_ (byteToBits b₁) (byteToBits b₂))
```

## Properties of Binary Representations

Helper lemma for `bitVal` and modulo 2 operation.

```
private
  bitVal-%2 : ∀ k → bitVal (k % 2 ≡ᵇ 1) ≡ k % 2
  bitVal-%2 k with k % 2 | m%n<n k 2
  ... | 0                | _ = refl
  ... | 1                | _ = refl
  ... | suc (suc _) | s≤s (s≤s ())
```

`bitsToByte` and `byteToBits` are mutual inverses.

```
bitsToByte-byteToBits : ∀ b → bitsToByte (byteToBits b) ≡ b
bitsToByte-byteToBits _ = refl

byteToBits-bitsToByte : ∀ bs → byteToBits (bitsToByte bs) ≡ bs
byteToBits-bitsToByte (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ []) = refl
```

`bitsToNat` is the left inverse of `natToBits`:

```
bitsToNat-natToBits : ∀ len k → k < 2 ^ len → bitsToNat (natToBits len k) ≡ k
bitsToNat-natToBits zero    zero (s≤s z≤n) = refl
bitsToNat-natToBits (suc len) k k<
  rewrite bitsToNat-natToBits len (k / 2)
            (m<n*o⇒m/o<n {k} {2 ^ len} {2} (subst (k <_) (*-comm 2 (2 ^ len)) k<))
        | bitVal-%2 k
        | *-comm 2 (k / 2)
        = sym (m≡m%n+[m/n]*n k 2)
```

`bitsToNat` is also the right inverse of `natToBits`:

```
private
  -- The lowest bit of `bitVal b + 2 * x` is `b` ...
  parity : ∀ b x → ((bitVal b + 2 * x) % 2 ≡ᵇ 1) ≡ b
  parity false x =
    cong (_≡ᵇ 1) (trans (cong (_% 2) (*-comm 2 x)) (m*n%n≡0 x 2))
  parity true  x =
    cong (_≡ᵇ 1) (trans (cong (λ r → (1 + r) % 2) (*-comm 2 x)) ([m+kn]%n≡m%n 1 x 2))

  -- ... and the remaining bits are `x`.
  half : ∀ b x → (bitVal b + 2 * x) / 2 ≡ x
  half false x = trans (cong (_/ 2) (*-comm 2 x)) (m*n/n≡m x 2)
  half true  x =
    trans (cong (λ r → (1 + r) / 2) (*-comm 2 x))
          (trans (+-distrib-/ 1 (x * 2) 1%2+x*2%2<2) (cong (1 / 2 +_) (m*n/n≡m x 2)))
    where
      1%2+x*2%2<2 : 1 % 2 + x * 2 % 2 < 2
      1%2+x*2%2<2 = subst (λ r → 1 % 2 + r < 2) (sym (m*n%n≡0 x 2)) (s≤s (s≤s z≤n))

natToBits-bitsToNat : ∀ len bs → natToBits len (bitsToNat bs) ≡ bs
natToBits-bitsToNat zero      []       = refl
natToBits-bitsToNat (suc len) (b ∷ bs) =
  cong₂ _∷_ (parity b x)
            (trans (cong (natToBits len) (half b x)) (natToBits-bitsToNat len bs))
  where
    x = bitsToNat bs
```

`natToBits len` is injective on numbers that fit in `len` bits: different numbers get
different bit representations.

```
natToBits-injective
  : ∀ len {n m}
  → n < 2 ^ len
  → m < 2 ^ len
  → natToBits len n ≡ natToBits len m
  → n ≡ m
natToBits-injective len {n} {m} n< m< eq =
  trans (sym (bitsToNat-natToBits len n n<))
        (trans (cong bitsToNat eq) (bitsToNat-natToBits len m m<))
```

For a given length, the bits of a `BinaryOf n` are determined by `n`: they are exactly
`natToBits len n`.

```
bits-canonical
  : ∀ {n} (x : BinaryOf n)
  → BinaryOf.bits x ≡ natToBits (BinaryOf.len x) n
bits-canonical {n} (binary l bs p) =
  recompute (Vec.≡-dec 𝔹._≟_ bs (natToBits l n))
            (trans (sym (natToBits-bitsToNat l bs)) (cong (natToBits l) p))
```

Every `n` fits in `suc ⌊log₂ n ⌋` bits.

```
private
  3+n≤2*[2+⌊n/2⌋] : ∀ n → 3 + n ≤ 2 * (2 + ⌊ n /2⌋)
  3+n≤2*[2+⌊n/2⌋] zero          = s≤s (s≤s (s≤s z≤n))
  3+n≤2*[2+⌊n/2⌋] (suc zero)    = ≤-refl
  3+n≤2*[2+⌊n/2⌋] (suc (suc n)) =
    s≤s (s≤s (s≤s (≤-trans (s≤s (s≤s⁻¹ (s≤s⁻¹ (3+n≤2*[2+⌊n/2⌋] n))))
                           (≤-reflexive (sym (+-suc h _))))))
    where h = ⌊ n /2⌋

  <2^suc⌊log2⌋ : ∀ n (rec : Acc _<_ n) → n < 2 ^ suc (⌊log2⌋ n rec)
  <2^suc⌊log2⌋ zero             _        = s≤s z≤n
  <2^suc⌊log2⌋ (suc zero)       _        = s≤s (s≤s z≤n)
  <2^suc⌊log2⌋ (suc n′@(suc n)) (acc rs) =
    ≤-trans (3+n≤2*[2+⌊n/2⌋] n)
            (*-monoʳ-≤ 2 (<2^suc⌊log2⌋ (suc ⌊ n /2⌋) (rs (⌊n/2⌋<n n′))))

n<2^suc⌊log₂n⌋ : ∀ n → n < 2 ^ suc ⌊log₂ n ⌋
n<2^suc⌊log₂n⌋ n = <2^suc⌊log2⌋ n _
```

## Smart Constructors for `BinaryOf`

`binaryOfLen len k` represents `k` using exactly `len` bits; the bound `k < 2 ^ len`
guarantees that no bits are truncated. `binaryOf n` uses the minimal number of bits,
`suc ⌊log₂ n ⌋`, so `0` is represented by a single `false` bit.

```
binaryOfLen : (len k : ℕ) → .(k < 2 ^ len) → BinaryOf k
binaryOfLen len k k< =
  binary len (natToBits len k) (bitsToNat-natToBits len k k<)

binaryOf : (n : ℕ) → BinaryOf n
binaryOf n = binaryOfLen (suc ⌊log₂ n ⌋) n (n<2^suc⌊log₂n⌋ n)
```
