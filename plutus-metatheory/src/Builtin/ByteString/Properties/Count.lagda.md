---
title: Builtin.ByteString.Properties.Count
layout: page
---

This module proves the laws of `countSetBits` and `findFirstSetBit` from the
second batch of bitwise builtins,
[CIP-123](https://cips.cardano.org/cip/CIP-0123). These are the counting and
searching properties tested by the Haskell test suite
`Evaluation.Builtins.Bitwise.CIP0123`:

* `countSetBits` is a monoid homomorphism from concatenation to addition, it
  is unchanged by rotations, the set bits of a bytestring and of its
  complement add up to the bit length, and it satisfies the
  inclusion-exclusion principle `|x xor y| = |x or y| - |x and y|`;
* `xor`ing a bytestring with itself leaves no set bits, so `countSetBits`
  gives 0 and `findFirstSetBit` gives -1;
* `findFirstSetBit` gives -1 on bytestrings of zero bytes, and otherwise an
  index whose bit is set and below which all bits are clear;
* the first set bit of a replicated byte is that of the byte, and appending
  zero bytes shifts the first set bit by eight per byte.

```
module Builtin.ByteString.Properties.Count where
```

## Imports

```
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; z≤n; s≤s)
import Data.Nat.Properties as ℕP
import Data.Nat.Solver as ℕS
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; 0ℤ; 1ℤ)
import Data.Integer.Properties as ℤP
import Data.Integer.Solver as ℤS
import Data.List as L
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Builtin.ByteString.Byte
open import Builtin.ByteString.Base
open import Builtin.ByteString.Denotation
open import Builtin.ByteString.Properties.Byte
open import Builtin.ByteString.Properties.Base
open import Builtin.ByteString.Properties.Logical using (xor-self)
open import Builtin.ByteString.Properties.ShiftRotate
  using (rotated; rotateBYTESTRING-fits; toBits-rotated)
```

## Arithmetic

```
private

  T⇒≡true : ∀ {b} → T b → b ≡ true
  T⇒≡true {true} _ = refl

  interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  interchange = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl
    where open ℕS.+-*-Solver

  -- If a + b = c then b = c - a, in the integers.
  pos-∸ : ∀ a b c → a + b ≡ c → + b ≡ + c ℤ.- + a
  pos-∸ a b c eq = begin
    + b
    ≡⟨ solve 2 (λ a b → b := (a :+ b) :- a) refl (+ a) (+ b) ⟩
    (+ a ℤ.+ + b) ℤ.- + a
    ≡⟨ cong (λ z → z ℤ.- + a) (cong +_ eq) ⟩
    + c ℤ.- + a
    ∎
    where open ℤS.+-*-Solver
```

## Counting set bits

The number of set bits of a bytestring, as a natural number, and of a list of
bits.

```
popCountBS : ByteString → ℕ
popCountBS [] = 0
popCountBS (x ∷ xs) = popCount x + popCountBS xs

countTrue : Bits* → ℕ
countTrue L.[] = 0
countTrue (b L.∷ bs) = bitVal b + countTrue bs

countSetBITS-popCountBS : ∀ bs → countSetBITS bs ≡ + popCountBS bs
countSetBITS-popCountBS [] = refl
countSetBITS-popCountBS (x ∷ xs) = cong (λ z → + popCount x ℤ.+ z) (countSetBITS-popCountBS xs)

countTrue-++ : ∀ xs ys → countTrue (xs L.++ ys) ≡ countTrue xs + countTrue ys
countTrue-++ L.[] ys = refl
countTrue-++ (x L.∷ xs) ys =
  trans (cong (ℕ._+_ (bitVal x)) (countTrue-++ xs ys)) (sym (ℕP.+-assoc (bitVal x) _ _))

popCountBS-countTrue : ∀ bs → popCountBS bs ≡ countTrue (toBits bs)
popCountBS-countTrue [] = refl
popCountBS-countTrue (x ∷ xs) = begin
  popCount x + popCountBS xs
  ≡⟨ cong (ℕ._+_ (popCount x)) (popCountBS-countTrue xs) ⟩
  popCount x + countTrue (toBits xs)
  ≡⟨ ℕP.+-comm (popCount x) _ ⟩
  countTrue (toBits xs) + popCount x
  ≡⟨ cong (ℕ._+_ (countTrue (toBits xs))) (countTrue-byteBits x) ⟨
  countTrue (toBits xs) + countTrue (byteBits x)
  ≡⟨ countTrue-++ (toBits xs) (byteBits x) ⟨
  countTrue (toBits xs L.++ byteBits x)
  ≡⟨ cong countTrue (toBits-∷ x xs) ⟨
  countTrue (toBits (x ∷ xs))
  ∎
  where
    countTrue-byteBits : ∀ x → countTrue (byteBits x) ≡ popCount x
    countTrue-byteBits (byte _ _ _ _ _ _ _ _) = refl
```

`countSetBits` turns concatenation into addition.

```
countSetBITS-[] : countSetBITS [] ≡ 0ℤ
countSetBITS-[] = refl

countSetBITS-concat : ∀ xs ys → countSetBITS (concat xs ys) ≡ countSetBITS xs ℤ.+ countSetBITS ys
countSetBITS-concat xs ys = begin
  countSetBITS (concat xs ys)
  ≡⟨ cong countSetBITS (concat≡++ᵇ xs ys) ⟩
  countSetBITS (xs ++ᵇ ys)
  ≡⟨ countSetBITS-popCountBS (xs ++ᵇ ys) ⟩
  + popCountBS (xs ++ᵇ ys)
  ≡⟨ cong +_ (popCountBS-++ᵇ xs ys) ⟩
  + popCountBS xs ℤ.+ + popCountBS ys
  ≡⟨ cong₂ ℤ._+_ (countSetBITS-popCountBS xs) (countSetBITS-popCountBS ys) ⟨
  countSetBITS xs ℤ.+ countSetBITS ys
  ∎
  where
    popCountBS-++ᵇ : ∀ xs ys → popCountBS (xs ++ᵇ ys) ≡ popCountBS xs + popCountBS ys
    popCountBS-++ᵇ [] ys = refl
    popCountBS-++ᵇ (x ∷ xs) ys =
      trans (cong (ℕ._+_ (popCount x)) (popCountBS-++ᵇ xs ys)) (sym (ℕP.+-assoc (popCount x) _ _))
```

Every bit is set either in a bytestring or in its complement.

```
countSetBITS-complement
  : ∀ bs → countSetBITS bs ≡ bitLength bs ℤ.- countSetBITS (complementBYTESTRING bs)
countSetBITS-complement bs = begin
  countSetBITS bs
  ≡⟨ countSetBITS-popCountBS bs ⟩
  + popCountBS bs
  ≡⟨ pos-∸ (popCountBS (complementBYTESTRING bs)) (popCountBS bs) (lengthℕ bs * 8) (count bs) ⟩
  + (lengthℕ bs * 8) ℤ.- + popCountBS (complementBYTESTRING bs)
  ≡⟨ cong₂ ℤ._-_ (bitLength-lengthℕ bs) (countSetBITS-popCountBS (complementBYTESTRING bs)) ⟨
  bitLength bs ℤ.- countSetBITS (complementBYTESTRING bs)
  ∎
  where
    count : ∀ bs → popCountBS (complementBYTESTRING bs) + popCountBS bs ≡ lengthℕ bs * 8
    count [] = refl
    count (x ∷ xs) =
      trans (interchange (popCount (notByte x)) (popCountBS (complementBYTESTRING xs))
                         (popCount x) (popCountBS xs))
            (cong₂ _+_ (popCount-not x) (count xs))
```

The inclusion-exclusion principle, under the truncation semantics.

```
countSetBITS-inclusion-exclusion
  : ∀ xs ys
  → countSetBITS (xorBYTESTRING false xs ys)
    ≡ countSetBITS (orBYTESTRING false xs ys) ℤ.- countSetBITS (andBYTESTRING false xs ys)
countSetBITS-inclusion-exclusion xs ys = begin
  countSetBITS (xorBYTESTRING false xs ys)
  ≡⟨ countSetBITS-popCountBS (xorBYTESTRING false xs ys) ⟩
  + popCountBS (xorBYTESTRING false xs ys)
  ≡⟨ pos-∸ (popCountBS (andBYTESTRING false xs ys)) _ _
       (trans (ℕP.+-comm (popCountBS (andBYTESTRING false xs ys)) _) (count xs ys)) ⟩
  + popCountBS (orBYTESTRING false xs ys) ℤ.- + popCountBS (andBYTESTRING false xs ys)
  ≡⟨ cong₂ ℤ._-_ (countSetBITS-popCountBS (orBYTESTRING false xs ys))
                 (countSetBITS-popCountBS (andBYTESTRING false xs ys)) ⟨
  countSetBITS (orBYTESTRING false xs ys) ℤ.- countSetBITS (andBYTESTRING false xs ys)
  ∎
  where
    count
      : ∀ xs ys
      → popCountBS (xorBYTESTRING false xs ys) + popCountBS (andBYTESTRING false xs ys)
        ≡ popCountBS (orBYTESTRING false xs ys)
    count [] [] = refl
    count [] (y ∷ ys) = refl
    count (x ∷ xs) [] = refl
    count (x ∷ xs) (y ∷ ys) =
      trans (interchange (popCount (xorByte x y)) _ (popCount (andByte x y)) _)
            (cong₂ _+_ (popCount-inclusion-exclusion x y) (count xs ys))
```

A bytestring `xor`ed with itself has no set bits.

```
private

  popCountBS-zeros : ∀ n → popCountBS (replicateBS n 0B) ≡ 0
  popCountBS-zeros zero = refl
  popCountBS-zeros (suc n) = popCountBS-zeros n

countSetBITS-xor-self : ∀ pad bs → countSetBITS (xorBYTESTRING pad bs bs) ≡ 0ℤ
countSetBITS-xor-self pad bs = begin
  countSetBITS (xorBYTESTRING pad bs bs)
  ≡⟨ cong countSetBITS (xor-self pad bs) ⟩
  countSetBITS (replicateBS (lengthℕ bs) 0B)
  ≡⟨ countSetBITS-popCountBS (replicateBS (lengthℕ bs) 0B) ⟩
  + popCountBS (replicateBS (lengthℕ bs) 0B)
  ≡⟨ cong +_ (popCountBS-zeros (lengthℕ bs)) ⟩
  0ℤ
  ∎
```

Rotations move bits around without changing them, so they keep the number of
set bits.

```
private

  countTrue-rotateBits : ∀ k bits → countTrue (rotateBits k bits) ≡ countTrue bits
  countTrue-rotateBits k L.[] = refl
  countTrue-rotateBits k bits@(x L.∷ xs) = begin
    countTrue (L.drop d bits L.++ L.take d bits)
    ≡⟨ countTrue-++ (L.drop d bits) (L.take d bits) ⟩
    countTrue (L.drop d bits) + countTrue (L.take d bits)
    ≡⟨ ℕP.+-comm (countTrue (L.drop d bits)) _ ⟩
    countTrue (L.take d bits) + countTrue (L.drop d bits)
    ≡⟨ countTrue-++ (L.take d bits) (L.drop d bits) ⟨
    countTrue (L.take d bits L.++ L.drop d bits)
    ≡⟨ cong countTrue (LP.take++drop≡id d bits) ⟩
    countTrue bits
    ∎
    where
      open import Data.Integer.DivMod using (_%ℕ_)
      d = L.length bits ℕ.∸ k %ℕ L.length bits

countSetBITS-rotate
  : ∀ bs k → fitsInt k ≡ true
  → (rotateBYTESTRING bs k >>= λ bs' → just (countSetBITS bs')) ≡ just (countSetBITS bs)
countSetBITS-rotate bs k fits rewrite rotateBYTESTRING-fits bs k fits = cong just (begin
  countSetBITS (rotated bs k)
  ≡⟨ countSetBITS-popCountBS (rotated bs k) ⟩
  + popCountBS (rotated bs k)
  ≡⟨ cong +_ (popCountBS-countTrue (rotated bs k)) ⟩
  + countTrue (toBits (rotated bs k))
  ≡⟨ cong (λ bits → + countTrue bits) (toBits-rotated bs k) ⟩
  + countTrue (rotateBits k (toBits bs))
  ≡⟨ cong +_ (countTrue-rotateBits k (toBits bs)) ⟩
  + countTrue (toBits bs)
  ≡⟨ cong +_ (popCountBS-countTrue bs) ⟨
  + popCountBS bs
  ≡⟨ countSetBITS-popCountBS bs ⟨
  countSetBITS bs
  ∎)
```

## Finding the first set bit

`firstSetBitFrom o` searches a list of bits, numbering them from `o`: it
either finds nothing, or an index at least `o`.

```
private

  noneSet : Bits* → Set
  noneSet bits = ∀ o → firstSetBitFrom o bits ≡ -[1+ 0 ]

  firstSetBitFrom-cases
    : ∀ o bits → (firstSetBitFrom o bits ≡ -[1+ 0 ]) ⊎ Σ ℕ (λ i → firstSetBitFrom o bits ≡ + i)
  firstSetBitFrom-cases o L.[] = inj₁ refl
  firstSetBitFrom-cases o (true L.∷ bits) = inj₂ (o , refl)
  firstSetBitFrom-cases o (false L.∷ bits) = firstSetBitFrom-cases (suc o) bits

  firstSetBitFrom-≥ : ∀ o bits x → firstSetBitFrom o bits ≡ + x → o ≤ x
  firstSetBitFrom-≥ o (true L.∷ bits) x eq = ℕP.≤-reflexive (ℤP.+-injective eq)
  firstSetBitFrom-≥ o (false L.∷ bits) x eq = ℕP.<⇒≤ (firstSetBitFrom-≥ (suc o) bits x eq)

  -- Whether a search finds nothing does not depend on the numbering.
  none-any : ∀ o bits → firstSetBitFrom o bits ≡ -[1+ 0 ] → noneSet bits
  none-any o L.[] _ o′ = refl
  none-any o (false L.∷ bits) eq o′ = none-any (suc o) bits eq (suc o′)

  -- Renumbering a successful search shifts the result.
  found-offset : ∀ o o′ bits i → firstSetBitFrom o bits ≡ + i → firstSetBitFrom (o′ + o) bits ≡ + (o′ + i)
  found-offset o o′ (true L.∷ bits) i eq = cong (λ z → + (o′ + z)) (ℤP.+-injective eq)
  found-offset o o′ (false L.∷ bits) i eq =
    trans (cong (λ z → firstSetBitFrom z bits) (sym (ℕP.+-suc o′ o)))
          (found-offset (suc o) o′ bits i eq)

  found-++ : ∀ o xs ys i → firstSetBitFrom o xs ≡ + i → firstSetBitFrom o (xs L.++ ys) ≡ + i
  found-++ o (true L.∷ xs) ys i eq = eq
  found-++ o (false L.∷ xs) ys i eq = found-++ (suc o) xs ys i eq

  none-++
    : ∀ o xs ys → firstSetBitFrom o xs ≡ -[1+ 0 ]
    → firstSetBitFrom o (xs L.++ ys) ≡ firstSetBitFrom (o + L.length xs) ys
  none-++ o L.[] ys _ = cong (λ z → firstSetBitFrom z ys) (sym (ℕP.+-identityʳ o))
  none-++ o (false L.∷ xs) ys eq =
    trans (none-++ (suc o) xs ys eq)
          (cong (λ z → firstSetBitFrom z ys) (sym (ℕP.+-suc o (L.length xs))))

  none-replicate : ∀ n → noneSet (L.replicate n false)
  none-replicate zero o = refl
  none-replicate (suc n) o = none-replicate n (suc o)
```

A successful search finds a set bit, and all the bits before it are clear.

```
private

  firstSetBitFrom-found
    : ∀ o bits i → firstSetBitFrom o bits ≡ + (o + i)
    → (lookupBit bits i ≡ just true) × (∀ j → j < i → lookupBit bits j ≡ just false)
  firstSetBitFrom-found o (true L.∷ bits) zero eq = refl , λ j ()
  firstSetBitFrom-found o (true L.∷ bits) (suc i) eq =
    contradiction (trans (ℤP.+-injective eq) (ℕP.+-suc o i)) (ℕP.m≢1+m+n o)
  firstSetBitFrom-found o (false L.∷ bits) zero eq =
    contradiction (firstSetBitFrom-≥ (suc o) bits (o + 0) eq) (ℕP.<⇒≱ (s≤s (ℕP.≤-reflexive (ℕP.+-identityʳ o))))
  firstSetBitFrom-found o (false L.∷ bits) (suc i) eq
    with firstSetBitFrom-found (suc o) bits i (trans eq (cong +_ (ℕP.+-suc o i)))
  ... | set , clear = set , clear′
    where
      clear′ : ∀ j → j < suc i → lookupBit (false L.∷ bits) j ≡ just false
      clear′ zero _ = refl
      clear′ (suc j) (s≤s j<i) = clear j j<i
```

The `findFirstSetBit` builtin.

```
findFirstSetBIT-index
  : ∀ bs i → findFirstSetBIT bs ≡ + i
  → (readBIT bs (+ i) ≡ just true) × (∀ j → j < i → readBIT bs (+ j) ≡ just false)
findFirstSetBIT-index bs i eq with firstSetBitFrom-found 0 (toBits bs) i eq
... | set , clear =
  trans (readBIT-lookupBit bs i) set , λ j j<i → trans (readBIT-lookupBit bs j) (clear j j<i)

findFirstSetBIT-zeros : ∀ n → findFirstSetBIT (replicateBS n 0B) ≡ -[1+ 0 ]
findFirstSetBIT-zeros n =
  trans (cong firstSetBit (toBits-zeros n)) (none-replicate (n * 8) 0)

findFirstSetBIT-xor-self : ∀ pad bs → findFirstSetBIT (xorBYTESTRING pad bs bs) ≡ -[1+ 0 ]
findFirstSetBIT-xor-self pad bs =
  trans (cong findFirstSetBIT (xor-self pad bs)) (findFirstSetBIT-zeros (lengthℕ bs))
```

Appending `m` zero bytes to a bytestring moves its first set bit up by `8m`:
the zero bytes contribute the lowest bits. With a single non-zero byte this is
the property that the first set bit of `b` followed by `m` zero bytes is
`8m` plus the number of trailing zeros of `b`.

```
findFirstSetBIT-zeros-suffix
  : ∀ bs m i → findFirstSetBIT bs ≡ + i
  → findFirstSetBIT (concat bs (replicateBS m 0B)) ≡ + (m * 8 + i)
findFirstSetBIT-zeros-suffix bs m i eq = begin
  firstSetBit (toBits (concat bs (replicateBS m 0B)))
  ≡⟨ cong (λ x → firstSetBit (toBits x)) (concat≡++ᵇ bs (replicateBS m 0B)) ⟩
  firstSetBit (toBits (bs ++ᵇ replicateBS m 0B))
  ≡⟨ cong firstSetBit (toBits-++ᵇ bs (replicateBS m 0B)) ⟩
  firstSetBit (toBits (replicateBS m 0B) L.++ toBits bs)
  ≡⟨ cong (λ zs → firstSetBit (zs L.++ toBits bs)) (toBits-zeros m) ⟩
  firstSetBit (L.replicate (m * 8) false L.++ toBits bs)
  ≡⟨ none-++ 0 (L.replicate (m * 8) false) (toBits bs) (none-replicate (m * 8) 0) ⟩
  firstSetBitFrom (L.length (L.replicate (m * 8) false)) (toBits bs)
  ≡⟨ cong (λ o → firstSetBitFrom o (toBits bs)) (LP.length-replicate (m * 8)) ⟩
  firstSetBitFrom (m * 8) (toBits bs)
  ≡⟨ cong (λ o → firstSetBitFrom o (toBits bs)) (sym (ℕP.+-identityʳ (m * 8))) ⟩
  firstSetBitFrom (m * 8 + 0) (toBits bs)
  ≡⟨ found-offset 0 (m * 8) (toBits bs) i eq ⟩
  + (m * 8 + i)
  ∎
```

Replicating a byte any positive number of times has the same first set bit as
the byte itself: either the first copy contains a set bit, or no copy does.

```
private

  none-concat-replicate : ∀ c → noneSet c → ∀ n → noneSet (L.concat (L.replicate n c))
  none-concat-replicate c none zero o = refl
  none-concat-replicate c none (suc n) o =
    trans (none-++ o c _ (none o)) (none-concat-replicate c none n (o + L.length c))

  firstSetBit-replicate
    : ∀ n x → firstSetBit (toBits (replicateBS (suc n) x)) ≡ firstSetBit (toBits (x ∷ []))
  firstSetBit-replicate n x
    rewrite toBits-replicateBS (suc n) x | toBits-replicateBS 1 x
    with firstSetBitFrom-cases 0 (byteBits x)
  ... | inj₂ (i , found) =
    trans (found-++ 0 c _ i found) (sym (found-++ 0 c L.[] i found))
    where c = byteBits x
  ... | inj₁ none =
    trans (none-++ 0 c rest none)
    (trans (none-concat-replicate c (none-any 0 c none) n (0 + L.length c))
           (sym (trans (none-++ 0 c L.[] none) refl)))
    where
      c = byteBits x
      rest = L.concat (L.replicate n c)

findFirstSetBIT-replicate
  : ∀ n w → suc n ≤ 8192
  → (replicateBYTE (+ suc n) w >>= λ bs → just (findFirstSetBIT bs))
    ≡ (replicateBYTE 1ℤ w >>= λ bs → just (findFirstSetBIT bs))
findFirstSetBIT-replicate n w n≤ with toByte w
... | nothing = refl
... | just x rewrite T⇒≡true (ℕP.≤⇒≤ᵇ n≤) = cong just (firstSetBit-replicate n x)
```
