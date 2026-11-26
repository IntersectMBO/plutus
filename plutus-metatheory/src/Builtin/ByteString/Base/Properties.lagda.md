---
title: Builtin.ByteString.Base.Properties
layout: page
---

```
module Builtin.ByteString.Base.Properties where
```

Properties of the ByteString library in `Builtin.ByteString.Base`, the pure definitions
behind the ByteString builtins:

* list laws for concatenation, reversal and length;
* round trips between natural numbers and their little- and big-endian ByteString
  encodings, in both directions;
* laws of the byte-wise and bit-level operations behind the logical and bitwise builtins,
  such as commutativity and De Morgan's laws, and laws for shifts, rotations, counting,
  searching and writing bits.

The corresponding laws for the builtins are in `Builtin.ByteString.Properties`.

## Imports

```
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; T; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _*_; _^_; _%_; _/_; _⊓_; _⊔_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.DivMod
  using (m%n<n; m%n%n≡m%n; m<n⇒m%n≡m; n%n≡0; %-distribˡ-+; [m+kn]%n≡m%n; m≡m%n+[m/n]*n)
open import Data.Nat.Properties using (+-assoc; *-assoc; *-distribˡ-+; +-identityʳ; ≤ᵇ⇒≤)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (recompute)

import Data.Fin as Fin
import Data.Fin.Properties as Fin
import Data.List as L
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
import Data.Vec as Vec
import Data.Vec.Properties as Vec

open import Builtin.Binary
  using (Bits; Byte; byte; bitVal; bitsToNat; bitsToByte; byteToBits; byteToNat;
         byteToBits-bitsToByte; bitsToByte-byteToBits; natToBits-bitsToNat; mapByte;
         zipWithByte; BinaryOf; binary; binaryOf; binaryOfLen)
open import Builtin.ByteString.Base
  using (ByteString; []; _∷_; _++_; length; reverseAcc; reverse; map; padTo;
         bitsToByteStringLE; natToByteStringLE; natToByteStringBE; natToByteStringLenLE;
         natToByteStringLenBE; byteStringToNatLE; byteStringToNatBE; toBitsLE; toVec;
         fromVec; toBits; fromBits; groupBytes; onBits; zipWithExtend; shiftLeft;
         shiftRight; shiftRightAt; rotateLeft; rotateRight; popCount; findFirstSet;
         setBits)
```

## Concatenation and Reversal

Standard list lemmas for ByteStrings. `reverse-involutive` is used to transfer results
about little-endian encodings to big-endian ones.

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

Reversal preserves the length.

```
length-reverseAcc : ∀ acc xs → length (reverseAcc acc xs) ≡ length xs + length acc
length-reverseAcc acc [] = refl
length-reverseAcc acc (x ∷ xs) =
  trans (length-reverseAcc (x ∷ acc) xs) (ℕₚ.+-suc (length xs) (length acc))

length-reverse : ∀ bs → length (reverse bs) ≡ length bs
length-reverse bs =
  trans (length-reverseAcc [] bs) (ℕₚ.+-identityʳ (length bs))
```

## Bits

Lemmas about the value `bitsToNat` of a bit vector.

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

A vector of `n` bits denotes a number below `2 ^ n`.

```
private
  1+2x<2m : ∀ {x m} → x < m → 1 + 2 * x < 2 * m
  1+2x<2m {x} {m} x<m = subst (_≤ 2 * m) (ℕₚ.*-suc 2 x) (ℕₚ.*-monoʳ-≤ 2 x<m)

bitsToNat-< : ∀ {n} (bs : Bits n) → bitsToNat bs < 2 ^ n
bitsToNat-< {n} [] = s≤s z≤n
bitsToNat-< {n} (false ∷ bs) = ℕₚ.<-trans (ℕₚ.n<1+n _) (1+2x<2m (bitsToNat-< bs))
bitsToNat-< {n} (true ∷ bs) = 1+2x<2m (bitsToNat-< bs)
```

## Bits to ByteString and back

Reading back the little-endian ByteString built from some bits yields the number those
bits denote, including when the last byte is padded.

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
  trans (cong (λ r → byteToNat (bitsToByte firstBits) + 256 * r)
              (byteStringToNatLE-bitsToByteStringLE bs))
        (sym (bitsToNat-++ firstBits bs))
  where firstBits = b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ []
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

Decoding the encoding of a natural number gives back that number, for both byte orders.
These are the facts behind `byteStringToInteger e (integerToByteString e w n) ≡ n` for the
inputs on which `integerToByteString` succeeds.

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

## Round Trips: ByteString → Natural Number → ByteString

Conversely, encoding the value of a ByteString of `w` bytes in `w` bytes gives back the
ByteString. The proof works on the bits of the ByteString, listed in little-endian order
by `toBitsLE`: `bitsToByteStringLE` turns them back into the ByteString, and `bitsToNat`
computes its value. Encoding that value with `natToByteStringLenLE` produces the same
bits, by `natToBits-bitsToNat`.

`toBitsLE bs` has `length bs * 8` bits, while `natToByteStringLenLE` works with
`8 * length bs` bits. `subst-Bits` says that transporting bits along an equation between
lengths changes neither their value nor the ByteString they form.

```
subst-Bits
  : ∀ {A : Set} (f : ∀ {k} → Bits k → A) {m n} (eq : m ≡ n) (bs : Bits m)
  → f (subst Bits eq bs) ≡ f bs
subst-Bits f refl bs = refl

bitsToByteStringLE-toBitsLE : ∀ bs → bitsToByteStringLE (toBitsLE bs) ≡ bs
bitsToByteStringLE-toBitsLE [] = refl
bitsToByteStringLE-toBitsLE (b ∷ bs) =
  cong₂ _∷_ (bitsToByte-byteToBits b) (bitsToByteStringLE-toBitsLE bs)

bitsToNat-toBitsLE : ∀ bs → bitsToNat (toBitsLE bs) ≡ byteStringToNatLE bs
bitsToNat-toBitsLE bs =
  trans
    (sym (byteStringToNatLE-bitsToByteStringLE (toBitsLE bs)))
    (cong byteStringToNatLE (bitsToByteStringLE-toBitsLE bs))
```

A ByteString of `w` bytes denotes a number below `2 ^ (8 * w)`.

```
byteStringToNatLE-< : ∀ bs → byteStringToNatLE bs < 2 ^ (8 * length bs)
byteStringToNatLE-< bs =
  subst
    (_< 2 ^ (8 * length bs))
    (trans (subst-Bits bitsToNat eq (toBitsLE bs)) (bitsToNat-toBitsLE bs))
    (bitsToNat-< (subst Bits eq (toBitsLE bs)))
  where eq = ℕₚ.*-comm (length bs) 8
```

The round trip itself. The length is an argument with an equation, so that the lemma also
applies to `reverse bs`, which is needed for the big-endian encoding.

```
natToByteStringLenLE-bitsToNat
  : ∀ w {n} (bs : Bits (8 * w)) .(p : n < 2 ^ (8 * w))
  → bitsToNat bs ≡ n
  → natToByteStringLenLE w n p ≡ bitsToByteStringLE bs
natToByteStringLenLE-bitsToNat w {n} bs p refl =
  cong bitsToByteStringLE (natToBits-bitsToNat (8 * w) bs)

natToByteStringLenLE-byteStringToNatLE
  : ∀ w bs → length bs ≡ w → .(p : byteStringToNatLE bs < 2 ^ (8 * w))
  → natToByteStringLenLE w (byteStringToNatLE bs) p ≡ bs
natToByteStringLenLE-byteStringToNatLE _ bs refl p =
  trans (natToByteStringLenLE-bitsToNat (length bs) bits p
          (trans (subst-Bits bitsToNat eq (toBitsLE bs)) (bitsToNat-toBitsLE bs)))
        (trans (subst-Bits bitsToByteStringLE eq (toBitsLE bs))
               (bitsToByteStringLE-toBitsLE bs))
  where
    eq   = ℕₚ.*-comm (length bs) 8
    bits = subst Bits eq (toBitsLE bs)
```

## Bitwise Operations

Properties of the pure building blocks behind the logical and bitwise builtins.

### Bytes

Bitwise operations on single bytes inherit the laws of the corresponding operations on
booleans, bit by bit.

```
private
  byte-cong
    : ∀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ : Bool}
    → a₁ ≡ b₁ → a₂ ≡ b₂ → a₃ ≡ b₃ → a₄ ≡ b₄ → a₅ ≡ b₅ → a₆ ≡ b₆ → a₇ ≡ b₇ → a₈ ≡ b₈
    → byte a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ ≡ byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
  byte-cong refl refl refl refl refl refl refl refl = refl

not-∧ : ∀ a b → not (a ∧ b) ≡ not a ∨ not b
not-∧ true  _ = refl
not-∧ false _ = refl

not-∨ : ∀ a b → not (a ∨ b) ≡ not a ∧ not b
not-∨ true  _ = refl
not-∨ false _ = refl

mapByte-involutive
  : ∀ {f : Bool → Bool} → (∀ b → f (f b) ≡ b) → ∀ x → mapByte f (mapByte f x) ≡ x
mapByte-involutive inv (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) =
  byte-cong (inv b₁) (inv b₂) (inv b₃) (inv b₄) (inv b₅) (inv b₆) (inv b₇) (inv b₈)

zipWithByte-comm
  : ∀ {f : Bool → Bool → Bool} → (∀ a b → f a b ≡ f b a)
  → ∀ x y → zipWithByte f x y ≡ zipWithByte f y x
zipWithByte-comm c (byte a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) =
  byte-cong (c a₁ b₁) (c a₂ b₂) (c a₃ b₃) (c a₄ b₄)
            (c a₅ b₅) (c a₆ b₆) (c a₇ b₇) (c a₈ b₈)

mapByte-zipWithByte
  : ∀ {g : Bool → Bool} {f f′ : Bool → Bool → Bool}
  → (∀ a b → g (f a b) ≡ f′ (g a) (g b))
  → ∀ x y → mapByte g (zipWithByte f x y) ≡ zipWithByte f′ (mapByte g x) (mapByte g y)
mapByte-zipWithByte h (byte a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) =
  byte-cong (h a₁ b₁) (h a₂ b₂) (h a₃ b₃) (h a₄ b₄)
            (h a₅ b₅) (h a₆ b₆) (h a₇ b₇) (h a₈ b₈)
```

### Byte-wise Operations on ByteStrings

Laws for `map` and `zipWithExtend`, from which the laws of the logical builtins follow.

```
length-map : ∀ f bs → length (map f bs) ≡ length bs
length-map f []       = refl
length-map f (_ ∷ bs) = cong suc (length-map f bs)

map-involutive : ∀ {g : Byte → Byte} → (∀ x → g (g x) ≡ x) → ∀ bs → map g (map g bs) ≡ bs
map-involutive inv []       = refl
map-involutive inv (x ∷ bs) = cong₂ _∷_ (inv x) (map-involutive inv bs)

zipWithExtend-comm
  : ∀ {f : Byte → Byte → Byte} → (∀ x y → f x y ≡ f y x)
  → ∀ e p xs ys → zipWithExtend f e p xs ys ≡ zipWithExtend f e p ys xs
zipWithExtend-comm c e     p []       []       = refl
zipWithExtend-comm c e     p (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (c x y) (zipWithExtend-comm c e p xs ys)
zipWithExtend-comm c false p []       (_ ∷ _)  = refl
zipWithExtend-comm c false p (_ ∷ _)  []       = refl
zipWithExtend-comm c true  p []       (y ∷ ys) =
  cong₂ _∷_ (c p y) (zipWithExtend-comm c true p [] ys)
zipWithExtend-comm c true  p (x ∷ xs) []       =
  cong₂ _∷_ (c x p) (zipWithExtend-comm c true p xs [])
```

Without extension the result is as long as the shorter input, with extension as long as
the longer one.

```
length-zipWithExtend-false
  : ∀ f p xs ys → length (zipWithExtend f false p xs ys) ≡ length xs ⊓ length ys
length-zipWithExtend-false f p []       []       = refl
length-zipWithExtend-false f p (_ ∷ xs) (_ ∷ ys) =
  cong suc (length-zipWithExtend-false f p xs ys)
length-zipWithExtend-false f p []       (_ ∷ _)  = refl
length-zipWithExtend-false f p (_ ∷ _)  []       = refl

length-zipWithExtend-true
  : ∀ f p xs ys → length (zipWithExtend f true p xs ys) ≡ length xs ⊔ length ys
length-zipWithExtend-true f p []       []       = refl
length-zipWithExtend-true f p (_ ∷ xs) (_ ∷ ys) =
  cong suc (length-zipWithExtend-true f p xs ys)
length-zipWithExtend-true f p []       (_ ∷ ys) =
  cong suc (length-zipWithExtend-true f p [] ys)
length-zipWithExtend-true f p (_ ∷ xs) []       =
  cong suc (trans (length-zipWithExtend-true f p xs []) (ℕₚ.⊔-identityʳ (length xs)))
```

A byte-wise map distributes over `zipWithExtend`, provided it maps the padding byte too.

```
map-zipWithExtend
  : ∀ {g : Byte → Byte} {f f′ : Byte → Byte → Byte}
  → (∀ x y → g (f x y) ≡ f′ (g x) (g y))
  → ∀ e p xs ys
  → map g (zipWithExtend f e p xs ys) ≡ zipWithExtend f′ e (g p) (map g xs) (map g ys)
map-zipWithExtend h e     p []       []       = refl
map-zipWithExtend h e     p (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (h x y) (map-zipWithExtend h e p xs ys)
map-zipWithExtend h false p []       (_ ∷ _)  = refl
map-zipWithExtend h false p (_ ∷ _)  []       = refl
map-zipWithExtend h true  p []       (y ∷ ys) =
  cong₂ _∷_ (h p y) (map-zipWithExtend h true p [] ys)
map-zipWithExtend h true  p (x ∷ xs) []       =
  cong₂ _∷_ (h x p) (map-zipWithExtend h true p xs [])
```

### Bit-level View

`toBits` and `fromBits` are inverse, in the sense that converting a ByteString to its bits
and back gives the original ByteString. The other direction holds only up to the length
index, so it is stated through `onBits`.

```
fromVec-toVec : ∀ bs → fromVec (toVec bs) ≡ bs
fromVec-toVec []       = refl
fromVec-toVec (b ∷ bs) = cong (b ∷_) (fromVec-toVec bs)

length-fromVec : ∀ {n} (v : Vec Byte n) → length (fromVec v) ≡ n
length-fromVec []      = refl
length-fromVec (_ ∷ v) = cong suc (length-fromVec v)

private
  consΣ : Byte → Σ ℕ (Vec Byte) → Σ ℕ (Vec Byte)
  consΣ b (k , w) = suc k , b ∷ w

  -- `toVec ∘ fromVec` is the identity, up to the length index.
  toVec-fromVec
    : ∀ {n} (v : Vec Byte n)
    → _≡_ {A = Σ ℕ (Vec Byte)} (length (fromVec v) , toVec (fromVec v)) (n , v)
  toVec-fromVec []      = refl
  toVec-fromVec (b ∷ v) = cong (consΣ b) (toVec-fromVec v)

concat-groupBytes
  : ∀ n (bits : Bits (n * 8)) → Vec.concat (Vec.map byteToBits (groupBytes n bits)) ≡ bits
concat-groupBytes zero    []                                         = refl
concat-groupBytes (suc n) (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ bits) =
  cong (λ r → b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ r) (concat-groupBytes n bits)

groupBytes-concat
  : ∀ {n} (v : Vec Byte n) → groupBytes n (Vec.concat (Vec.map byteToBits v)) ≡ v
groupBytes-concat []                                    = refl
groupBytes-concat (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ ∷ v) =
  cong (byte b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ ∷_) (groupBytes-concat v)

fromBits-toBits : ∀ bs → fromBits (length bs) (toBits bs) ≡ bs
fromBits-toBits bs =
  trans (cong (λ v → fromVec (Vec.reverse v))
              (groupBytes-concat (Vec.reverse (toVec bs))))
        (trans (cong fromVec (Vec.reverse-involutive (toVec bs))) (fromVec-toVec bs))

length-fromBits : ∀ n bits → length (fromBits n bits) ≡ n
length-fromBits n bits = length-fromVec (Vec.reverse (groupBytes n bits))
```

`onBits` preserves the length, is the identity when the bit operation is, and composes.

```
length-onBits : ∀ (f : ∀ {n} → Bits n → Bits n) bs → length (onBits f bs) ≡ length bs
length-onBits f bs = length-fromBits (length bs) (f (toBits bs))

onBits-id
  : ∀ (f : ∀ {n} → Bits n → Bits n) bs → f (toBits bs) ≡ toBits bs → onBits f bs ≡ bs
onBits-id f bs eq = trans (cong (fromBits (length bs)) eq) (fromBits-toBits bs)

onBits-fromVec
  : ∀ (f : ∀ {n} → Bits n → Bits n) {n} (v : Vec Byte n)
  → onBits f (fromVec v)
  ≡ fromBits n (f (Vec.concat (Vec.map byteToBits (Vec.reverse v))))
onBits-fromVec f v = cong G (toVec-fromVec v)
  where
    G : Σ ℕ (Vec Byte) → ByteString
    G (k , w) = fromBits k (f (Vec.concat (Vec.map byteToBits (Vec.reverse w))))

onBits-∘
  : ∀ (f g : ∀ {n} → Bits n → Bits n) bs
  → onBits f (onBits g bs) ≡ onBits (λ v → f (g v)) bs
onBits-∘ f g bs =
  trans (onBits-fromVec f (Vec.reverse (groupBytes n x)))
        (cong (λ v → fromBits n (f v))
              (trans (cong (λ w → Vec.concat (Vec.map byteToBits w))
                           (Vec.reverse-involutive (groupBytes n x)))
                     (concat-groupBytes n x)))
  where
    n = length bs
    x = g (toBits bs)
```

### Shifts

Shifting by zero is the identity.

```
private
  fromℕ<-cong
    : ∀ {m m′ n} .{p : m < n} .{q : m′ < n} → m ≡ m′ → Fin.fromℕ< p ≡ Fin.fromℕ< q
  fromℕ<-cong refl = refl

  tabulate-false : ∀ n → Vec.tabulate {n = n} (λ _ → false) ≡ Vec.replicate n false
  tabulate-false zero    = refl
  tabulate-false (suc n) = cong (false ∷_) (tabulate-false n)

  if-false : ∀ {b} {x : Bool} → b ≡ false → (if b then x else false) ≡ false
  if-false refl = refl

  ≤ᵇ-false : ∀ {n} k (i : Fin n) → n ≤ k → (k ℕ.≤ᵇ Fin.toℕ i) ≡ false
  ≤ᵇ-false k i n≤k with k ℕ.≤ᵇ Fin.toℕ i in eq
  ... | false = refl
  ... | true  = ⊥-elim (ℕₚ.<-irrefl refl
                 (ℕₚ.<-≤-trans (Fin.toℕ<n i)
                   (ℕₚ.≤-trans n≤k (≤ᵇ⇒≤ k (Fin.toℕ i) (subst T (sym eq) tt)))))

shiftLeft-zero : ∀ {n} (bs : Bits n) → shiftLeft 0 bs ≡ bs
shiftLeft-zero bs =
  trans (Vec.tabulate-cong λ i → cong (Vec.lookup bs) (Fin.fromℕ<-toℕ i (Fin.toℕ<n i)))
        (Vec.tabulate∘lookup bs)

shiftRightAt-zero : ∀ {n} (bs : Bits n) i → shiftRightAt 0 bs i ≡ Vec.lookup bs i
shiftRightAt-zero {n} bs i with Fin.toℕ i + 0 ℕ.<? n
... | yes _ =
  cong (Vec.lookup bs)
       (trans (fromℕ<-cong {q = Fin.toℕ<n i} (+-identityʳ (Fin.toℕ i)))
              (Fin.fromℕ<-toℕ i (Fin.toℕ<n i)))
... | no ¬p = ⊥-elim (¬p (subst (_< n) (sym (+-identityʳ (Fin.toℕ i))) (Fin.toℕ<n i)))

shiftRight-zero : ∀ {n} (bs : Bits n) → shiftRight 0 bs ≡ bs
shiftRight-zero bs =
  trans (Vec.tabulate-cong (shiftRightAt-zero bs)) (Vec.tabulate∘lookup bs)
```

Shifting by at least the length clears every bit.

```
shiftLeft-overflow
  : ∀ {n} k (bs : Bits n) → n ≤ k → shiftLeft k bs ≡ Vec.replicate n false
shiftLeft-overflow k bs n≤k =
  trans (Vec.tabulate-cong λ i → if-false (≤ᵇ-false k i n≤k)) (tabulate-false _)

shiftRightAt-overflow : ∀ {n} k (bs : Bits n) → n ≤ k → ∀ i → shiftRightAt k bs i ≡ false
shiftRightAt-overflow {n} k bs n≤k i with Fin.toℕ i + k ℕ.<? n
... | no _  = refl
... | yes p = ⊥-elim (ℕₚ.<-irrefl refl
                (ℕₚ.<-≤-trans (ℕₚ.≤-<-trans (ℕₚ.m≤n+m k (Fin.toℕ i)) p) n≤k))

shiftRight-overflow
  : ∀ {n} k (bs : Bits n) → n ≤ k → shiftRight k bs ≡ Vec.replicate n false
shiftRight-overflow k bs n≤k =
  trans (Vec.tabulate-cong (shiftRightAt-overflow k bs n≤k)) (tabulate-false _)
```

### Rotations

Rotations by `a` and then `b` compose to a rotation by `a + b`, and rotating by a multiple
of the length is the identity. Both follow from modular arithmetic on the indices.

```
private
  %-addˡ : ∀ x b N .{{_ : ℕ.NonZero N}} → (x % N + b) % N ≡ (x + b) % N
  %-addˡ x b N =
    trans (%-distribˡ-+ (x % N) b N)
          (trans (cong (λ y → (y + b % N) % N) (m%n%n≡m%n x N))
                 (sym (%-distribˡ-+ x b N)))

  -- Rotating right by `N ∸ k % N` and then by `k` is a full turn.
  sub-mod : ∀ k n → (suc n ∸ k % suc n + k) % suc n ≡ 0
  sub-mod k n =
    trans (cong (λ x → (N ∸ r + x) % N) (m≡m%n+[m/n]*n k N))
          (trans (cong (_% N) (sym (+-assoc (N ∸ r) r (q * N))))
                 (trans (cong (λ x → (x + q * N) % N) (ℕₚ.m∸n+n≡m (ℕₚ.<⇒≤ (m%n<n k N))))
                        ([m+kn]%n≡m%n 0 (suc q) N)))
    where
      N = suc n
      r = k % N
      q = k / N

rotateRight-rotateRight
  : ∀ {n} a b (bs : Bits n) → rotateRight a (rotateRight b bs) ≡ rotateRight (a + b) bs
rotateRight-rotateRight {zero}  a b bs = refl
rotateRight-rotateRight {suc n} a b bs =
  Vec.tabulate-cong λ i →
    trans (Vec.lookup∘tabulate
             (λ j → Vec.lookup bs (Fin.fromℕ< (m%n<n (Fin.toℕ j + b) N)))
             (Fin.fromℕ< (m%n<n (Fin.toℕ i + a) N)))
          (cong (Vec.lookup bs) (fromℕ<-cong {q = m%n<n (Fin.toℕ i + (a + b)) N} (eq i)))
  where
    N = suc n
    eq : ∀ i → (Fin.toℕ (Fin.fromℕ< (m%n<n (Fin.toℕ i + a) N)) + b) % N
             ≡ (Fin.toℕ i + (a + b)) % N
    eq i =
      trans (cong (λ x → (x + b) % N) (Fin.toℕ-fromℕ< (m%n<n (Fin.toℕ i + a) N)))
            (trans (%-addˡ (Fin.toℕ i + a) b N)
                   (cong (_% N) (+-assoc (Fin.toℕ i) a b)))

rotateRight-id : ∀ {n} a (bs : Bits (suc n)) → a % suc n ≡ 0 → rotateRight a bs ≡ bs
rotateRight-id {n} a bs a%N≡0 =
  trans (Vec.tabulate-cong λ i →
           cong (Vec.lookup bs)
                (trans (fromℕ<-cong {p = m%n<n (Fin.toℕ i + a) N} {q = Fin.toℕ<n i}
                                    (eq i))
                       (Fin.fromℕ<-toℕ i (Fin.toℕ<n i))))
        (Vec.tabulate∘lookup bs)
  where
    N = suc n
    eq : ∀ i → (Fin.toℕ i + a) % N ≡ Fin.toℕ i
    eq i =
      trans (%-distribˡ-+ (Fin.toℕ i) a N)
            (trans (cong (λ y → (Fin.toℕ i % N + y) % N) a%N≡0)
                   (trans (cong (_% N) (+-identityʳ (Fin.toℕ i % N)))
                          (trans (m%n%n≡m%n (Fin.toℕ i) N) (m<n⇒m%n≡m (Fin.toℕ<n i)))))

rotateRight-zero : ∀ {n} (bs : Bits n) → rotateRight 0 bs ≡ bs
rotateRight-zero {zero}  bs = refl
rotateRight-zero {suc n} bs = rotateRight-id 0 bs refl

rotateLeft-zero : ∀ {n} (bs : Bits n) → rotateLeft 0 bs ≡ bs
rotateLeft-zero {zero}  bs = refl
rotateLeft-zero {suc n} bs = rotateRight-id (suc n) bs (n%n≡0 (suc n))
```

Left and right rotations by the same amount are mutually inverse.

```
rotateLeft-rotateRight : ∀ {n} k (bs : Bits n) → rotateLeft k (rotateRight k bs) ≡ bs
rotateLeft-rotateRight {zero}  k bs = refl
rotateLeft-rotateRight {suc n} k bs =
  trans (rotateRight-rotateRight (suc n ∸ k % suc n) k bs)
        (rotateRight-id _ bs (sub-mod k n))

rotateRight-rotateLeft : ∀ {n} k (bs : Bits n) → rotateRight k (rotateLeft k bs) ≡ bs
rotateRight-rotateLeft {zero}  k bs = refl
rotateRight-rotateLeft {suc n} k bs =
  trans (rotateRight-rotateRight k (suc n ∸ k % suc n) bs)
        (rotateRight-id _ bs (trans (cong (_% suc n) (ℕₚ.+-comm k _)) (sub-mod k n)))
```

### Counting, Searching and Writing Bits

There are at most `n` set bits in a vector of length `n`.

```
popCount-≤ : ∀ {n} (bs : Bits n) → popCount bs ≤ n
popCount-≤ []           = z≤n
popCount-≤ (false ∷ bs) = ℕₚ.m≤n⇒m≤1+n (popCount-≤ bs)
popCount-≤ (true  ∷ bs) = s≤s (popCount-≤ bs)
```

`findFirstSet` returns the lowest set bit, or `nothing` if no bit is set.

```
findFirstSet-lookup
  : ∀ {n} (bs : Bits n) {i} → findFirstSet bs ≡ just i → Vec.lookup bs i ≡ true
findFirstSet-lookup (true  ∷ _)  refl = refl
findFirstSet-lookup (false ∷ bs) eq with findFirstSet bs in e
findFirstSet-lookup (false ∷ bs) refl | just _  = findFirstSet-lookup bs e
findFirstSet-lookup (false ∷ bs) ()   | nothing

findFirstSet-minimal
  : ∀ {n} (bs : Bits n) {i} → findFirstSet bs ≡ just i
  → ∀ j → j Fin.< i → Vec.lookup bs j ≡ false
findFirstSet-minimal (true  ∷ _)  refl j ()
findFirstSet-minimal (false ∷ bs) eq j j<i with findFirstSet bs in e
findFirstSet-minimal (false ∷ bs) refl Fin.zero    _   | just _ = refl
findFirstSet-minimal (false ∷ bs) refl (Fin.suc j) j<i | just _ =
  findFirstSet-minimal bs e j (ℕ.s<s⁻¹ j<i)
findFirstSet-minimal (false ∷ bs) () _ _ | nothing

findFirstSet-nothing
  : ∀ {n} (bs : Bits n) → findFirstSet bs ≡ nothing → ∀ i → Vec.lookup bs i ≡ false
findFirstSet-nothing (true  ∷ _)  () _
findFirstSet-nothing (false ∷ bs) eq i with findFirstSet bs in e
findFirstSet-nothing (false ∷ bs) () _           | just _
findFirstSet-nothing (false ∷ bs) _  Fin.zero    | nothing = refl
findFirstSet-nothing (false ∷ bs) _  (Fin.suc i) | nothing = findFirstSet-nothing bs e i
```

After `setBits is u`, the bits at the indices in `is` are `u` and all others are
unchanged.

```
lookup-setBits-∈
  : ∀ {n} {i : Fin n} is u (bs : Bits n) → i ∈ is → Vec.lookup (setBits is u bs) i ≡ u
lookup-setBits-∈ (j L.∷ is) u bs (here refl) = Vec.lookup∘update j (setBits is u bs) u
lookup-setBits-∈ {i = i} (j L.∷ is) u bs (there p) with j Fin.≟ i
... | yes refl = Vec.lookup∘update j (setBits is u bs) u
... | no j≢i   =
  trans (Vec.lookup∘update′ (λ i≡j → j≢i (sym i≡j)) (setBits is u bs) u)
        (lookup-setBits-∈ is u bs p)

lookup-setBits-∉
  : ∀ {n} {i : Fin n} is u (bs : Bits n) → i ∉ is
  → Vec.lookup (setBits is u bs) i ≡ Vec.lookup bs i
lookup-setBits-∉ L.[]       u bs _  = refl
lookup-setBits-∉ (j L.∷ is) u bs i∉ =
  trans (Vec.lookup∘update′ (λ i≡j → i∉ (here i≡j)) (setBits is u bs) u)
        (lookup-setBits-∉ is u bs (λ p → i∉ (there p)))
```
