---
title: Builtin.ByteString.Properties
layout: page
---

```
module Builtin.ByteString.Properties where
```

Properties of the ByteString builtins in `Builtin.ByteString`, derived from the
properties of the ByteString library in `Builtin.ByteString.Base.Properties`:

* `byteStringToInteger` and `integerToByteString` are mutually inverse, and decoding a
  single byte gives its value, as required by CIP-121;
* algebraic laws of the logical builtins, such as commutativity and De Morgan's laws;
* laws for shifts, rotations, counting and searching.

The laws are stated for the builtins that cannot fail, and for `integerToByteString` and
`consByteString` on the inputs on which they succeed.

## Imports

```
open import Data.Bool using (true; false; not; _∧_; _∨_; _xor_)
open import Data.Bool.Properties using (not-involutive; ∧-comm; ∨-comm)
open import Data.Empty using (⊥-elim)
open import Data.Integer using (-[1+_]) renaming (+_ to pos)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; _+_; _*_; _^_; _⊓_; _⊔_; _<_; _≤_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Vec using ([]; _∷_)
open import Function.Base using (const)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

import Data.Fin as Fin
import Data.Fin.Properties as Fin
import Data.Integer as ℤ
import Data.Nat as ℕ
import Data.Vec as Vec
import Data.Vec.Properties as Vec

open import Builtin.Binary
  using (Bits; byteToNat; bitsToNat-natToBits; natToByte; fillByte; mapByte; zipWithByte)
open import Builtin.ByteString.Base
  using ([]; _∷_; length; reverse; replicate; byteStringToNatLE; fromVec; toBits;
         fromBits; groupBytes; shiftLeft; shiftRight; rotateLeft; rotateRight; popCount;
         findFirstSet)
open import Builtin.ByteString
  using (consByteStringV2; integerToByteString; byteStringToInteger; andByteString;
         orByteString; xorByteString; complementByteString; shiftByteString;
         rotateByteString; countSetBits; findFirstSetBit)
open import Builtin.ByteString.Base.Properties
  using (reverse-involutive; length-reverse; byteStringToNatLE-natToByteStringLE;
         byteStringToNatBE-natToByteStringBE; byteStringToNatLE-natToByteStringLenLE;
         byteStringToNatBE-natToByteStringLenBE; byteStringToNatLE-<;
         natToByteStringLenLE-byteStringToNatLE; not-∧; not-∨; mapByte-involutive;
         zipWithByte-comm; mapByte-zipWithByte; length-map; map-involutive;
         zipWithExtend-comm; length-zipWithExtend-false; length-zipWithExtend-true;
         map-zipWithExtend; length-onBits; onBits-id; onBits-∘; shiftLeft-zero;
         shiftLeft-overflow; shiftRight-overflow; rotateLeft-zero;
         rotateLeft-rotateRight; rotateRight-rotateLeft; popCount-≤;
         findFirstSet-nothing)
```

## The Conversion Builtins

Whenever `integerToByteString` succeeds, `byteStringToInteger` with the same byte order
gives back the original integer. This generalises the first property required of
`byteStringToInteger` in
[CIP-121](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0121#builtinbytestringtointeger),
`byteStringToInteger e (integerToByteString e 0 q) = q`, from the minimal width `0` to
every width. The CIP leaves the bounds of `integerToByteString` out of the property; here
they appear as the hypothesis that it succeeds.

The proof follows the cases of `integerToByteString`:
the empty encoding of `0`, the minimal-width encoding, the fixed-width encoding, and the
failing cases.

```
byteStringToInteger-integerToByteString
  : ∀ e w n {bs}
  → integerToByteString e w n ≡ just bs
  → byteStringToInteger e bs ≡ n
byteStringToInteger-integerToByteString true  (pos 0) (pos 0) refl = refl
byteStringToInteger-integerToByteString false (pos 0) (pos 0) refl = refl
byteStringToInteger-integerToByteString e (pos 0) (pos (suc n)) eq
  with suc n ℕ.<? 2 ^ 65536
byteStringToInteger-integerToByteString true  (pos 0) (pos (suc n)) refl | yes p =
  cong pos (byteStringToNatBE-natToByteStringBE (suc n) p)
byteStringToInteger-integerToByteString false (pos 0) (pos (suc n)) refl | yes p =
  cong pos (byteStringToNatLE-natToByteStringLE (suc n) p)
byteStringToInteger-integerToByteString _     (pos 0) (pos (suc _)) ()   | no _
byteStringToInteger-integerToByteString e (pos (suc w)) (pos n) eq
  with suc w ℕ.≤? 8192 | n ℕ.<? 2 ^ (8 * suc w)
byteStringToInteger-integerToByteString true  (pos (suc w)) (pos n) refl | yes _ | yes p =
  cong pos (byteStringToNatBE-natToByteStringLenBE (suc w) n p)
byteStringToInteger-integerToByteString false (pos (suc w)) (pos n) refl | yes _ | yes p =
  cong pos (byteStringToNatLE-natToByteStringLenLE (suc w) n p)
byteStringToInteger-integerToByteString _ (pos (suc _)) (pos _) () | yes _ | no _
byteStringToInteger-integerToByteString _ (pos (suc _)) (pos _) () | no _  | _
byteStringToInteger-integerToByteString _ (pos 0)       -[1+ _ ] ()
byteStringToInteger-integerToByteString _ (pos (suc _)) -[1+ _ ] ()
byteStringToInteger-integerToByteString _ -[1+ _ ]      _        ()
```

Decoding a single byte gives its value. This is the second property required of
`byteStringToInteger` in
[CIP-121](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0121#builtinbytestringtointeger),
where the byte is given by `consByteString`.

```
private
  byteToNat-natToByte : ∀ n (p : n < 2 ^ 8) → byteToNat (natToByte n p) + 256 * 0 ≡ n
  byteToNat-natToByte n p =
    trans (+-identityʳ _) (bitsToNat-natToBits 8 n p)

byteStringToInteger-consByteString
  : ∀ e n {bs}
  → consByteStringV2 (pos n) [] ≡ just bs
  → byteStringToInteger e bs ≡ pos n
byteStringToInteger-consByteString e n eq with n ℕ.<? 2 ^ 8
byteStringToInteger-consByteString true  n refl | yes p =
  cong pos (byteToNat-natToByte n p)
byteStringToInteger-consByteString false n refl | yes p =
  cong pos (byteToNat-natToByte n p)
byteStringToInteger-consByteString _     _ ()   | no _
```

Conversely, encoding the value of a ByteString with its own length as the width gives
back the ByteString. This is the third property required of `byteStringToInteger` in
CIP-121. Here it needs the hypothesis that the length is at most 8192, the largest width
`integerToByteString` accepts. It follows from the corresponding round trip for natural
numbers in `Builtin.ByteString.Base.Properties`.

The builtin-level statement. The empty ByteString is encoded with width `0`, which
`integerToByteString` treats separately. The other cases are proved by the two lemmas
below, one for each byte order, which take the width `suc w` as an argument with an
equation `length bs ≡ suc w`. Matching `bs` against `_ ∷ _` in their statements instead
would let Agda unfold `byteStringToNatLE (b ∷ bs)` into `byteToNat b + 256 * …`, which
makes the goals very large when they are displayed.

```
integerToByteString-byteStringToInteger-LE
  : ∀ w bs → length bs ≡ suc w → suc w ≤ 8192
  → integerToByteString false (pos (suc w)) (pos (byteStringToNatLE bs)) ≡ just bs
integerToByteString-byteStringToInteger-LE w bs eq len≤
  with suc w ℕ.≤? 8192 | byteStringToNatLE bs ℕ.<? 2 ^ (8 * suc w)
... | yes _    | yes p =
  cong just (natToByteStringLenLE-byteStringToNatLE _ bs eq p)
... | yes _    | no ¬p =
  ⊥-elim (¬p (subst (λ w → byteStringToNatLE bs < 2 ^ (8 * w)) eq
                    (byteStringToNatLE-< bs)))
... | no ¬len≤ | _     = ⊥-elim (¬len≤ len≤)

integerToByteString-byteStringToInteger-BE
  : ∀ w bs → length bs ≡ suc w → suc w ≤ 8192
  → integerToByteString true (pos (suc w)) (pos (byteStringToNatLE (reverse bs)))
  ≡ just bs
integerToByteString-byteStringToInteger-BE w bs eq len≤
  with suc w ℕ.≤? 8192 | byteStringToNatLE (reverse bs) ℕ.<? 2 ^ (8 * suc w)
... | yes _    | yes p =
  cong just
    (trans (cong reverse (natToByteStringLenLE-byteStringToNatLE
                            _ (reverse bs) (trans (length-reverse bs) eq) p))
           (reverse-involutive bs))
... | yes _    | no ¬p =
  ⊥-elim (¬p (subst (λ w → byteStringToNatLE (reverse bs) < 2 ^ (8 * w))
                    (trans (length-reverse bs) eq)
                    (byteStringToNatLE-< (reverse bs))))
... | no ¬len≤ | _     = ⊥-elim (¬len≤ len≤)

integerToByteString-byteStringToInteger
  : ∀ e bs → length bs ≤ 8192
  → integerToByteString e (pos (length bs)) (byteStringToInteger e bs) ≡ just bs
integerToByteString-byteStringToInteger true  []         _    = refl
integerToByteString-byteStringToInteger false []         _    = refl
integerToByteString-byteStringToInteger true  bs@(_ ∷ _) len≤ =
  integerToByteString-byteStringToInteger-BE _ bs refl len≤
integerToByteString-byteStringToInteger false bs@(_ ∷ _) len≤ =
  integerToByteString-byteStringToInteger-LE _ bs refl len≤
```

## The Logical Builtins

The logical builtins are commutative, complement is an involution, and De Morgan's laws
hold for both truncation and extension (the padding bytes are swapped as well).

```
private
  xor-comm : ∀ a b → a xor b ≡ b xor a
  xor-comm true  true  = refl
  xor-comm true  false = refl
  xor-comm false true  = refl
  xor-comm false false = refl

andByteString-comm : ∀ e xs ys → andByteString e xs ys ≡ andByteString e ys xs
andByteString-comm e = zipWithExtend-comm (zipWithByte-comm ∧-comm) e (fillByte true)

orByteString-comm : ∀ e xs ys → orByteString e xs ys ≡ orByteString e ys xs
orByteString-comm e = zipWithExtend-comm (zipWithByte-comm ∨-comm) e (fillByte false)

xorByteString-comm : ∀ e xs ys → xorByteString e xs ys ≡ xorByteString e ys xs
xorByteString-comm e = zipWithExtend-comm (zipWithByte-comm xor-comm) e (fillByte false)

length-andByteString-false
  : ∀ xs ys → length (andByteString false xs ys) ≡ length xs ⊓ length ys
length-andByteString-false = length-zipWithExtend-false (zipWithByte _∧_) (fillByte true)

length-andByteString-true
  : ∀ xs ys → length (andByteString true xs ys) ≡ length xs ⊔ length ys
length-andByteString-true = length-zipWithExtend-true (zipWithByte _∧_) (fillByte true)

length-complementByteString : ∀ bs → length (complementByteString bs) ≡ length bs
length-complementByteString = length-map (mapByte not)

complementByteString-involutive
  : ∀ bs → complementByteString (complementByteString bs) ≡ bs
complementByteString-involutive =
  map-involutive {g = mapByte not} (mapByte-involutive {f = not} not-involutive)

complement-andByteString
  : ∀ e xs ys
  → complementByteString (andByteString e xs ys)
  ≡ orByteString e (complementByteString xs) (complementByteString ys)
complement-andByteString e =
  map-zipWithExtend {g = mapByte not} {f = zipWithByte _∧_} {f′ = zipWithByte _∨_}
    (mapByte-zipWithByte {g = not} {f = _∧_} {f′ = _∨_} not-∧) e (fillByte true)

complement-orByteString
  : ∀ e xs ys
  → complementByteString (orByteString e xs ys)
  ≡ andByteString e (complementByteString xs) (complementByteString ys)
complement-orByteString e =
  map-zipWithExtend {g = mapByte not} {f = zipWithByte _∨_} {f′ = zipWithByte _∧_}
    (mapByte-zipWithByte {g = not} {f = _∨_} {f′ = _∧_} not-∨) e (fillByte false)
```

## The Bit-level Builtins

The laws for bit vectors in `Builtin.ByteString.Base.Properties` carry over to the
builtins through `onBits`.

### Shifts

Shifting by zero is the identity, and shifting by at least the length in bits clears every
bit. Both shifts and rotations preserve the length.

```
private
  reverse-replicate
    : ∀ {A : Set} n (x : A) → Vec.reverse (Vec.replicate n x) ≡ Vec.replicate n x
  reverse-replicate n x =
    trans (cong Vec.reverse (sym (Vec.map-const w x)))
          (trans (sym (Vec.map-reverse (const x) w)) (Vec.map-const (Vec.reverse w) x))
    where w = Vec.replicate n x

  groupBytes-replicate
    : ∀ n → groupBytes n (Vec.replicate (n * 8) false) ≡ Vec.replicate n (fillByte false)
  groupBytes-replicate zero    = refl
  groupBytes-replicate (suc n) = cong (fillByte false ∷_) (groupBytes-replicate n)

  fromVec-replicate : ∀ n b → fromVec (Vec.replicate n b) ≡ replicate n b
  fromVec-replicate zero    b = refl
  fromVec-replicate (suc n) b = cong (b ∷_) (fromVec-replicate n b)

  fromBits-replicate
    : ∀ n → fromBits n (Vec.replicate (n * 8) false) ≡ replicate n (fillByte false)
  fromBits-replicate n =
    trans (cong (λ v → fromVec (Vec.reverse v)) (groupBytes-replicate n))
          (trans (cong fromVec (reverse-replicate n (fillByte false)))
                 (fromVec-replicate n (fillByte false)))

length-shiftByteString : ∀ bs k → length (shiftByteString bs k) ≡ length bs
length-shiftByteString bs (pos k)    = length-onBits (shiftLeft k) bs
length-shiftByteString bs -[1+ k ] = length-onBits (shiftRight (suc k)) bs

shiftByteString-zero : ∀ bs → shiftByteString bs (pos 0) ≡ bs
shiftByteString-zero bs = onBits-id (shiftLeft 0) bs (shiftLeft-zero (toBits bs))

shiftByteString-overflow
  : ∀ bs k → length bs * 8 ≤ ℤ.∣ k ∣
  → shiftByteString bs k ≡ replicate (length bs) (fillByte false)
shiftByteString-overflow bs (pos k) n≤k =
  trans (cong (fromBits (length bs)) (shiftLeft-overflow k (toBits bs) n≤k))
        (fromBits-replicate (length bs))
shiftByteString-overflow bs -[1+ k ] n≤k =
  trans (cong (fromBits (length bs)) (shiftRight-overflow (suc k) (toBits bs) n≤k))
        (fromBits-replicate (length bs))
```

### Rotations

Rotating by zero is the identity, and rotating by `k` and then by `- k` gets back the
input.

```
length-rotateByteString : ∀ bs k → length (rotateByteString bs k) ≡ length bs
length-rotateByteString bs (pos k)    = length-onBits (rotateLeft k) bs
length-rotateByteString bs -[1+ k ] = length-onBits (rotateRight (suc k)) bs

rotateByteString-zero : ∀ bs → rotateByteString bs (pos 0) ≡ bs
rotateByteString-zero bs = onBits-id (rotateLeft 0) bs (rotateLeft-zero (toBits bs))

rotateByteString-inverse : ∀ bs k → rotateByteString (rotateByteString bs k) (ℤ.- k) ≡ bs
rotateByteString-inverse bs (pos zero) =
  trans (rotateByteString-zero (rotateByteString bs (pos 0))) (rotateByteString-zero bs)
rotateByteString-inverse bs (pos (suc k)) =
  trans (onBits-∘ (rotateRight (suc k)) (rotateLeft (suc k)) bs)
        (onBits-id (λ v → rotateRight (suc k) (rotateLeft (suc k) v)) bs
                   (rotateRight-rotateLeft (suc k) (toBits bs)))
rotateByteString-inverse bs -[1+ k ] =
  trans (onBits-∘ (rotateLeft (suc k)) (rotateRight (suc k)) bs)
        (onBits-id (λ v → rotateLeft (suc k) (rotateRight (suc k) v)) bs
                   (rotateLeft-rotateRight (suc k) (toBits bs)))
```

### Counting and Searching

```
private
  popCount-zero : ∀ {n} (bs : Bits n) → (∀ i → Vec.lookup bs i ≡ false) → popCount bs ≡ 0
  popCount-zero []       _ = refl
  popCount-zero (b ∷ bs) h with b | h Fin.zero
  ... | false | _ = popCount-zero bs (λ i → h (Fin.suc i))
  ... | true  | ()

countSetBits-≤ : ∀ bs → countSetBits bs ℤ.≤ pos (length bs * 8)
countSetBits-≤ bs = ℤ.+≤+ (popCount-≤ (toBits bs))
```

`findFirstSetBit` returns `-1` only if no bit is set.

```
findFirstSetBit-none : ∀ bs → findFirstSetBit bs ≡ -[1+ 0 ] → countSetBits bs ≡ pos 0
findFirstSetBit-none bs eq with findFirstSet (toBits bs) in e
findFirstSetBit-none bs () | just _
findFirstSetBit-none bs _  | nothing =
  cong pos (popCount-zero (toBits bs) (findFirstSet-nothing (toBits bs) e))
```
