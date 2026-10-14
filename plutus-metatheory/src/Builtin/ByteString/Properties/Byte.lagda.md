---
title: Builtin.ByteString.Properties.Byte
layout: page
---

This module proves the properties of single bytes (`Builtin.ByteString.Byte`)
that the bytestring properties are built on:

* the laws of the bitwise lifted operations `zipByte` and `mapByte`, inherited
  bit by bit from the corresponding laws on `Bool`;
* the population count of combinations of bytes;
* `byteToℕ` and `ℕToByte` are mutually inverse on `[0, 255]`;
* a decision procedure for properties of all 256 bytes, used to check
  statements about single bytes by evaluation.

```
module Builtin.ByteString.Properties.Byte where
```

## Imports

```
open import Data.Bool using (Bool; true; false; _∧_; _∨_; _xor_; not; if_then_else_; T)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; z≤n; s≤s; _≤ᵇ_)
open import Data.Nat.Base using (⌊_/2⌋; parity)
import Data.Nat.Properties as ℕP
open import Data.Vec.Base using (Vec; []; _∷_; zipWith) renaming (map to vmap)
import Data.Integer as ℤ using (+_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)

open import Builtin.ByteString.Byte
```

## Bitwise lifting

The byte with every bit equal to `b`; in particular `constByte false` is `0B`
and `constByte true` is `255B`.

```
constByte : Bool → Byte
constByte b = byte b b b b b b b b
```

Two bytes are equal when their bits are.

```
private

  cong-byte
    : ∀ {x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈}
    → x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → x₄ ≡ y₄
    → x₅ ≡ y₅ → x₆ ≡ y₆ → x₇ ≡ y₇ → x₈ ≡ y₈
    → byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ ≡ byte y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈
  cong-byte refl refl refl refl refl refl refl refl = refl
```

Every law of a boolean operation that is an equation between bitwise
expressions transfers to the bitwise lifted operation on bytes. The laws below
are the ones the bytestring proofs use.

```
module _ {f : Bool → Bool → Bool} where

  zipByte-comm
    : (∀ a b → f a b ≡ f b a)
    → ∀ x y → zipByte f x y ≡ zipByte f y x
  zipByte-comm c (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (byte y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈) =
    cong-byte (c x₁ y₁) (c x₂ y₂) (c x₃ y₃) (c x₄ y₄) (c x₅ y₅) (c x₆ y₆) (c x₇ y₇) (c x₈ y₈)

  zipByte-assoc
    : (∀ a b c → f (f a b) c ≡ f a (f b c))
    → ∀ x y z → zipByte f (zipByte f x y) z ≡ zipByte f x (zipByte f y z)
  zipByte-assoc c (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (byte y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈)
                  (byte z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈) =
    cong-byte (c x₁ y₁ z₁) (c x₂ y₂ z₂) (c x₃ y₃ z₃) (c x₄ y₄ z₄)
              (c x₅ y₅ z₅) (c x₆ y₆ z₆) (c x₇ y₇ z₇) (c x₈ y₈ z₈)

  zipByte-idem : (∀ a → f a a ≡ a) → ∀ x → zipByte f x x ≡ x
  zipByte-idem c (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =
    cong-byte (c x₁) (c x₂) (c x₃) (c x₄) (c x₅) (c x₆) (c x₇) (c x₈)

  zipByte-diag : ∀ {e} → (∀ a → f a a ≡ e) → ∀ x → zipByte f x x ≡ constByte e
  zipByte-diag c (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =
    cong-byte (c x₁) (c x₂) (c x₃) (c x₄) (c x₅) (c x₆) (c x₇) (c x₈)

  zipByte-identityˡ : ∀ {e} → (∀ a → f e a ≡ a) → ∀ x → zipByte f (constByte e) x ≡ x
  zipByte-identityˡ c (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =
    cong-byte (c x₁) (c x₂) (c x₃) (c x₄) (c x₅) (c x₆) (c x₇) (c x₈)

  zipByte-identityʳ : ∀ {e} → (∀ a → f a e ≡ a) → ∀ x → zipByte f x (constByte e) ≡ x
  zipByte-identityʳ c (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =
    cong-byte (c x₁) (c x₂) (c x₃) (c x₄) (c x₅) (c x₆) (c x₇) (c x₈)

  zipByte-distribˡ
    : ∀ {g} → (∀ a b c → f a (g b c) ≡ g (f a b) (f a c))
    → ∀ x y z → zipByte f x (zipByte g y z) ≡ zipByte g (zipByte f x y) (zipByte f x z)
  zipByte-distribˡ c (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (byte y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈)
                     (byte z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈) =
    cong-byte (c x₁ y₁ z₁) (c x₂ y₂ z₂) (c x₃ y₃ z₃) (c x₄ y₄ z₄)
              (c x₅ y₅ z₅) (c x₆ y₆ z₆) (c x₇ y₇ z₇) (c x₈ y₈ z₈)

  zipByte-involute
    : (∀ a → f a (f a a) ≡ a)
    → ∀ x → zipByte f x (zipByte f x x) ≡ x
  zipByte-involute c (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =
    cong-byte (c x₁) (c x₂) (c x₃) (c x₄) (c x₅) (c x₆) (c x₇) (c x₈)

module _ {h : Bool → Bool} where

  mapByte-involutive : (∀ a → h (h a) ≡ a) → ∀ x → mapByte h (mapByte h x) ≡ x
  mapByte-involutive c (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =
    cong-byte (c x₁) (c x₂) (c x₃) (c x₄) (c x₅) (c x₆) (c x₇) (c x₈)

  mapByte-zipByte
    : ∀ {f g} → (∀ a b → h (f a b) ≡ g (h a) (h b))
    → ∀ x y → mapByte h (zipByte f x y) ≡ zipByte g (mapByte h x) (mapByte h y)
  mapByte-zipByte c (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (byte y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈) =
    cong-byte (c x₁ y₁) (c x₂ y₂) (c x₃ y₃) (c x₄ y₄) (c x₅ y₅) (c x₆ y₆) (c x₇ y₇) (c x₈ y₈)
```

## Population count

`countBits` counts the set bits of a bit vector, and `popCount` those of a
byte. The value of a single bit, as used by `countBits` and `bitsToℕ`:

```
bitVal : Bool → ℕ
bitVal b = if b then 1 else 0
```

The inclusion–exclusion principle for bits: a bit is set in `x ∨ y` exactly
when it is set in `x xor y` or in `x ∧ y`, and never in both.

```
countBits-inclusion-exclusion
  : ∀ {n} (u v : Vec Bool n)
  → countBits (zipWith _xor_ u v) + countBits (zipWith _∧_ u v) ≡ countBits (zipWith _∨_ u v)
countBits-inclusion-exclusion [] [] = refl
countBits-inclusion-exclusion (true ∷ u) (true ∷ v) =
  trans (ℕP.+-suc (countBits (zipWith _xor_ u v)) _)
        (cong suc (countBits-inclusion-exclusion u v))
countBits-inclusion-exclusion (true ∷ u) (false ∷ v) = cong suc (countBits-inclusion-exclusion u v)
countBits-inclusion-exclusion (false ∷ u) (true ∷ v) = cong suc (countBits-inclusion-exclusion u v)
countBits-inclusion-exclusion (false ∷ u) (false ∷ v) = countBits-inclusion-exclusion u v
```

Every bit is set either in `u` or in its complement.

```
countBits-not : ∀ {n} (u : Vec Bool n) → countBits (vmap not u) + countBits u ≡ n
countBits-not [] = refl
countBits-not (true ∷ u) = trans (ℕP.+-suc (countBits (vmap not u)) _) (cong suc (countBits-not u))
countBits-not (false ∷ u) = cong suc (countBits-not u)
```

The byte versions.

```
popCount-inclusion-exclusion
  : ∀ x y → popCount (xorByte x y) + popCount (andByte x y) ≡ popCount (orByte x y)
popCount-inclusion-exclusion (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (byte y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈) =
  countBits-inclusion-exclusion
    (x₈ ∷ x₇ ∷ x₆ ∷ x₅ ∷ x₄ ∷ x₃ ∷ x₂ ∷ x₁ ∷ [])
    (y₈ ∷ y₇ ∷ y₆ ∷ y₅ ∷ y₄ ∷ y₃ ∷ y₂ ∷ y₁ ∷ [])

popCount-not : ∀ x → popCount (notByte x) + popCount x ≡ 8
popCount-not (byte x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =
  countBits-not (x₈ ∷ x₇ ∷ x₆ ∷ x₅ ∷ x₄ ∷ x₃ ∷ x₂ ∷ x₁ ∷ [])
```

## Conversion to and from numbers

`byteToBits` and `bitsToByte` are mutually inverse.

```
byteToBits-bitsToByte : ∀ v → byteToBits (bitsToByte v) ≡ v
byteToBits-bitsToByte (b₈ ∷ b₇ ∷ b₆ ∷ b₅ ∷ b₄ ∷ b₃ ∷ b₂ ∷ b₁ ∷ []) = refl

bitsToByte-byteToBits : ∀ x → bitsToByte (byteToBits x) ≡ x
bitsToByte-byteToBits (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) = refl
```

The binary representation of a number: its lowest bit plus twice the rest.
These facts about `parity` and `⌊_/2⌋` are proved by induction in steps of
two, following the definitions of those functions.

```
private

  bitVal-parity : ∀ k → bitVal (parityBit (parity k)) + 2 * ⌊ k /2⌋ ≡ k
  bitVal-parity 0 = refl
  bitVal-parity 1 = refl
  bitVal-parity (suc (suc k)) =
    trans (cong (b +_) (ℕP.*-suc 2 ⌊ k /2⌋))
    (trans (ℕP.+-suc b (suc (2 * ⌊ k /2⌋)))
    (cong suc (trans (ℕP.+-suc b (2 * ⌊ k /2⌋)) (cong suc (bitVal-parity k)))))
    where b = bitVal (parityBit (parity k))

  bitVal+2*suc : ∀ b r → bitVal b + 2 * suc r ≡ suc (suc (bitVal b + 2 * r))
  bitVal+2*suc b r =
    trans (cong (bitVal b +_) (ℕP.*-suc 2 r))
    (trans (ℕP.+-suc (bitVal b) (suc (2 * r))) (cong suc (ℕP.+-suc (bitVal b) (2 * r))))

  parity-bitVal : ∀ b r → parityBit (parity (bitVal b + 2 * r)) ≡ b
  parity-bitVal true zero = refl
  parity-bitVal false zero = refl
  parity-bitVal b (suc r) =
    trans (cong (λ k → parityBit (parity k)) (bitVal+2*suc b r)) (parity-bitVal b r)

  half-bitVal : ∀ b r → ⌊ bitVal b + 2 * r /2⌋ ≡ r
  half-bitVal true zero = refl
  half-bitVal false zero = refl
  half-bitVal b (suc r) =
    trans (cong ⌊_/2⌋ (bitVal+2*suc b r)) (cong suc (half-bitVal b r))

  bitVal≤1 : ∀ b → bitVal b ≤ 1
  bitVal≤1 true = s≤s z≤n
  bitVal≤1 false = z≤n

  -- If x < m then appending a bit to x stays below 2m.
  bitVal+2*<2* : ∀ b x m → x < m → bitVal b + 2 * x < 2 * m
  bitVal+2*<2* b x m x<m =
    ℕP.≤-trans (s≤s (ℕP.+-monoˡ-≤ (2 * x) (bitVal≤1 b)))
      (ℕP.≤-trans (ℕP.≤-reflexive (sym (ℕP.*-suc 2 x))) (ℕP.*-monoʳ-≤ 2 x<m))

  half< : ∀ k m → k < 2 * m → ⌊ k /2⌋ < m
  half< k m k<2m = ℕP.*-cancelˡ-< 2 _ _
    (ℕP.≤-<-trans (ℕP.≤-trans (ℕP.m≤n+m (2 * ⌊ k /2⌋) (bitVal (parityBit (parity k)))) (ℕP.≤-reflexive (bitVal-parity k))) k<2m)
```

Reading the bits of a number and converting back gives the number, as long as
it fits; converting bits to a number and back gives the bits.

```
bitsToℕ-ℕToBits : ∀ n k → k < 2 ^ n → bitsToℕ n (ℕToBits n k) ≡ k
bitsToℕ-ℕToBits zero zero _ = refl
bitsToℕ-ℕToBits zero (suc k) (s≤s ())
bitsToℕ-ℕToBits (suc n) k k<2^n =
  trans (cong (λ r → bitVal (parityBit (parity k)) + 2 * r)
              (bitsToℕ-ℕToBits n ⌊ k /2⌋ (half< k (2 ^ n) k<2^n)))
        (bitVal-parity k)

ℕToBits-bitsToℕ : ∀ n (v : Bits n) → ℕToBits n (bitsToℕ n v) ≡ v
ℕToBits-bitsToℕ zero [] = refl
ℕToBits-bitsToℕ (suc n) (b ∷ v)
  rewrite parity-bitVal b (bitsToℕ n v)
        | half-bitVal b (bitsToℕ n v)
        | ℕToBits-bitsToℕ n v = refl

bitsToℕ<2^n : ∀ n (v : Bits n) → bitsToℕ n v < 2 ^ n
bitsToℕ<2^n zero [] = s≤s z≤n
bitsToℕ<2^n (suc n) (b ∷ v) = bitVal+2*<2* b (bitsToℕ n v) (2 ^ n) (bitsToℕ<2^n n v)
```

The byte versions.

```
byteToℕ-ℕToByte : ∀ k → k < 256 → byteToℕ (ℕToByte k) ≡ k
byteToℕ-ℕToByte k k<256 =
  trans (cong (bitsToℕ 8) (byteToBits-bitsToByte (ℕToBits 8 k))) (bitsToℕ-ℕToBits 8 k k<256)

ℕToByte-byteToℕ : ∀ x → ℕToByte (byteToℕ x) ≡ x
ℕToByte-byteToℕ x =
  trans (cong bitsToByte (ℕToBits-bitsToℕ 8 (byteToBits x))) (bitsToByte-byteToBits x)

byteToℕ<256 : ∀ x → byteToℕ x < 256
byteToℕ<256 x = bitsToℕ<2^n 8 (byteToBits x)

byteToℕ-injective : ∀ {x y} → byteToℕ x ≡ byteToℕ y → x ≡ y
byteToℕ-injective {x} {y} eq =
  trans (sym (ℕToByte-byteToℕ x)) (trans (cong ℕToByte eq) (ℕToByte-byteToℕ y))
```

Converting a valid byte value with `toByte` succeeds.

```
private

  T⇒≡true : ∀ {b} → T b → b ≡ true
  T⇒≡true {true} _ = refl

toByte-valid : ∀ k → k < 256 → toByte (ℤ.+ k) ≡ just (ℕToByte k)
toByte-valid k (s≤s k≤255) rewrite T⇒≡true (ℕP.≤⇒≤ᵇ k≤255) = refl
```

## Deciding properties of all bytes

There are only 256 bytes, so a boolean-valued property can be checked for all
of them by evaluation. `allBytes p` evaluates `p` on every byte, and
`allBytes-sound` turns a successful check (proved by `refl`) into a proof for
every byte. This is used for statements about single bytes whose general
proofs would be needlessly arithmetic.

```
private

  ∧-trueˡ : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-trueˡ {true} _ = refl

  ∧-trueʳ : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧-trueʳ {true} h = h

  allBits : ∀ n → (Bits n → Bool) → Bool
  allBits zero p = p []
  allBits (suc n) p = allBits n (λ v → p (false ∷ v)) ∧ allBits n (λ v → p (true ∷ v))

  allBits-sound : ∀ n p → allBits n p ≡ true → ∀ v → p v ≡ true
  allBits-sound zero p h [] = h
  allBits-sound (suc n) p h (false ∷ v) = allBits-sound n _ (∧-trueˡ h) v
  allBits-sound (suc n) p h (true ∷ v) = allBits-sound n _ (∧-trueʳ {allBits n (λ v → p (false ∷ v))} h) v

allBytes : (Byte → Bool) → Bool
allBytes p = allBits 8 (λ v → p (bitsToByte v))

allBytes-sound : ∀ p → allBytes p ≡ true → ∀ x → p x ≡ true
allBytes-sound p h x =
  trans (cong p (sym (bitsToByte-byteToBits x)))
        (allBits-sound 8 (λ v → p (bitsToByte v)) h (byteToBits x))
```
