---
title: Builtin.ByteString.Properties.Base
layout: page
---

This module proves the basic properties of the bytestring operations in
`Builtin.ByteString.Base`, which the proofs of the builtin laws build on:

* lengths, concatenation and replication;
* the bitstring view: `toBits` and `fromBits` are mutually inverse, and
  `toBits` turns concatenation of bytestrings into (reversed) concatenation of
  bit lists;
* bit lists are determined by their `lookupBit`s, and the effect of `setBit`
  on them;
* `readBIT` is just `lookupBit` on the bitstring view, and `writeBITS`
  applies `setBit` on it.

```
module Builtin.ByteString.Properties.Base where
```

## Imports

```
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; z≤n; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; +<+)
import Data.Integer.Properties as ℤP
import Data.List as L
import Data.List.Properties as LP
open import Data.Bool.ListAction using (all)
open import Data.Vec.Base using (_∷_; []) renaming (toList to vecToList)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
import Data.Maybe.Properties as MP
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (yes; no; dec-true; dec-false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Builtin.ByteString.Byte
open import Builtin.ByteString.Base
open import Builtin.ByteString.Denotation
  using (lengthBS; concat; bitLength; validBitIndex; readBIT; writeBITS)
open import Builtin.ByteString.Properties.Byte
```

## Lists

A fact about lists missing from the standard library.

```
replicate-++ : ∀ {A : Set} m n (x : A) → L.replicate m x L.++ L.replicate n x ≡ L.replicate (m + n) x
replicate-++ zero n x = refl
replicate-++ (suc m) n x = cong (x L.∷_) (replicate-++ m n x)
```

## Lengths, concatenation and replication

```
lengthBS-lengthℕ : ∀ bs → lengthBS bs ≡ + lengthℕ bs
lengthBS-lengthℕ [] = refl
lengthBS-lengthℕ (_ ∷ xs) = cong (λ n → + 1 ℤ.+ n) (lengthBS-lengthℕ xs)

bitLength-lengthℕ : ∀ bs → bitLength bs ≡ + (lengthℕ bs * 8)
bitLength-lengthℕ bs =
  trans (cong (ℤ._* + 8) (lengthBS-lengthℕ bs)) (sym (ℤP.pos-* (lengthℕ bs) 8))

concat≡++ᵇ : ∀ xs ys → concat xs ys ≡ xs ++ᵇ ys
concat≡++ᵇ [] ys = refl
concat≡++ᵇ (x ∷ xs) ys = cong (x ∷_) (concat≡++ᵇ xs ys)

++ᵇ-identityʳ : ∀ xs → xs ++ᵇ [] ≡ xs
++ᵇ-identityʳ [] = refl
++ᵇ-identityʳ (x ∷ xs) = cong (x ∷_) (++ᵇ-identityʳ xs)

lengthℕ-++ᵇ : ∀ xs ys → lengthℕ (xs ++ᵇ ys) ≡ lengthℕ xs + lengthℕ ys
lengthℕ-++ᵇ [] ys = refl
lengthℕ-++ᵇ (x ∷ xs) ys = cong suc (lengthℕ-++ᵇ xs ys)

lengthℕ-replicateBS : ∀ n b → lengthℕ (replicateBS n b) ≡ n
lengthℕ-replicateBS zero b = refl
lengthℕ-replicateBS (suc n) b = cong suc (lengthℕ-replicateBS n b)

replicateBS-+ : ∀ m n b → replicateBS m b ++ᵇ replicateBS n b ≡ replicateBS (m + n) b
replicateBS-+ zero n b = refl
replicateBS-+ (suc m) n b = cong (b ∷_) (replicateBS-+ m n b)

lengthℕ-mapBS : ∀ f xs → lengthℕ (mapBS f xs) ≡ lengthℕ xs
lengthℕ-mapBS f [] = refl
lengthℕ-mapBS f (x ∷ xs) = cong suc (lengthℕ-mapBS f xs)
```

## The bitstring view

The bits of a single byte, least significant first.

```
byteBits : Byte → Bits*
byteBits x = vecToList (byteToBits x)

length-byteBits : ∀ x → L.length (byteBits x) ≡ 8
length-byteBits (byte _ _ _ _ _ _ _ _) = refl
```

`toBits` lists the bits of the last byte first, so it reverses the order of
the bytes. Unfolding its accumulator:

```
toBitsAcc-++ : ∀ acc xs → toBitsAcc acc xs ≡ toBits xs L.++ acc
toBitsAcc-++ acc [] = refl
toBitsAcc-++ acc (x ∷ xs) = begin
  toBitsAcc (byteBits x L.++ acc) xs
  ≡⟨ toBitsAcc-++ (byteBits x L.++ acc) xs ⟩
  toBits xs L.++ (byteBits x L.++ acc)
  ≡⟨ LP.++-assoc (toBits xs) (byteBits x) acc ⟨
  (toBits xs L.++ byteBits x) L.++ acc
  ≡⟨ cong (λ bits → (toBits xs L.++ bits) L.++ acc) (LP.++-identityʳ (byteBits x)) ⟨
  (toBits xs L.++ (byteBits x L.++ L.[])) L.++ acc
  ≡⟨ cong (L._++ acc) (toBitsAcc-++ (byteBits x L.++ L.[]) xs) ⟨
  toBits (x ∷ xs) L.++ acc
  ∎

toBits-∷ : ∀ x xs → toBits (x ∷ xs) ≡ toBits xs L.++ byteBits x
toBits-∷ x xs =
  trans (toBitsAcc-++ (byteBits x L.++ L.[]) xs)
        (cong (toBits xs L.++_) (LP.++-identityʳ (byteBits x)))

toBits-++ᵇ : ∀ xs ys → toBits (xs ++ᵇ ys) ≡ toBits ys L.++ toBits xs
toBits-++ᵇ [] ys = sym (LP.++-identityʳ (toBits ys))
toBits-++ᵇ (x ∷ xs) ys = begin
  toBits (x ∷ (xs ++ᵇ ys))
  ≡⟨ toBits-∷ x (xs ++ᵇ ys) ⟩
  toBits (xs ++ᵇ ys) L.++ byteBits x
  ≡⟨ cong (L._++ byteBits x) (toBits-++ᵇ xs ys) ⟩
  (toBits ys L.++ toBits xs) L.++ byteBits x
  ≡⟨ LP.++-assoc (toBits ys) (toBits xs) (byteBits x) ⟩
  toBits ys L.++ (toBits xs L.++ byteBits x)
  ≡⟨ cong (toBits ys L.++_) (toBits-∷ x xs) ⟨
  toBits ys L.++ toBits (x ∷ xs)
  ∎

length-toBits : ∀ bs → L.length (toBits bs) ≡ lengthℕ bs * 8
length-toBits [] = refl
length-toBits (x ∷ xs) = begin
  L.length (toBits (x ∷ xs))
  ≡⟨ cong L.length (toBits-∷ x xs) ⟩
  L.length (toBits xs L.++ byteBits x)
  ≡⟨ LP.length-++ (toBits xs) ⟩
  L.length (toBits xs) + L.length (byteBits x)
  ≡⟨ cong (ℕ._+_ (L.length (toBits xs))) (length-byteBits x) ⟩
  L.length (toBits xs) + 8
  ≡⟨ cong (_+ 8) (length-toBits xs) ⟩
  lengthℕ xs * 8 + 8
  ≡⟨ ℕP.+-comm (lengthℕ xs * 8) 8 ⟩
  lengthℕ (x ∷ xs) * 8
  ∎
```

`fromBits` consumes the bits a byte at a time, consing each byte onto its
accumulator, so it undoes the reversal performed by `toBits`.

```
fromBitsAcc-toBits
  : ∀ acc xs rest → fromBitsAcc acc (toBits xs L.++ rest) ≡ fromBitsAcc (xs ++ᵇ acc) rest
fromBitsAcc-toBits acc [] rest = refl
fromBitsAcc-toBits acc (x ∷ xs) rest = begin
  fromBitsAcc acc (toBits (x ∷ xs) L.++ rest)
  ≡⟨ cong (λ bits → fromBitsAcc acc (bits L.++ rest)) (toBits-∷ x xs) ⟩
  fromBitsAcc acc ((toBits xs L.++ byteBits x) L.++ rest)
  ≡⟨ cong (fromBitsAcc acc) (LP.++-assoc (toBits xs) (byteBits x) rest) ⟩
  fromBitsAcc acc (toBits xs L.++ (byteBits x L.++ rest))
  ≡⟨ fromBitsAcc-toBits acc xs (byteBits x L.++ rest) ⟩
  fromBitsAcc (xs ++ᵇ acc) (byteBits x L.++ rest)
  ≡⟨ fromBitsAcc-byteBits (xs ++ᵇ acc) x rest ⟩
  fromBitsAcc (x ∷ (xs ++ᵇ acc)) rest
  ∎
  where
    fromBitsAcc-byteBits
      : ∀ acc x rest → fromBitsAcc acc (byteBits x L.++ rest) ≡ fromBitsAcc (x ∷ acc) rest
    fromBitsAcc-byteBits acc (byte _ _ _ _ _ _ _ _) rest = refl

fromBits-toBits : ∀ bs → fromBits (toBits bs) ≡ bs
fromBits-toBits bs = begin
  fromBits (toBits bs)
  ≡⟨ cong (fromBitsAcc []) (LP.++-identityʳ (toBits bs)) ⟨
  fromBitsAcc [] (toBits bs L.++ L.[])
  ≡⟨ fromBitsAcc-toBits [] bs L.[] ⟩
  bs ++ᵇ []
  ≡⟨ ++ᵇ-identityʳ bs ⟩
  bs
  ∎
```

Conversely, a list of bits whose length is a multiple of eight is the bit
view of the bytestring `fromBits` makes of it.

```
toBits-fromBitsAcc
  : ∀ m acc bits → L.length bits ≡ m * 8
  → toBits (fromBitsAcc acc bits) ≡ toBits acc L.++ bits
toBits-fromBitsAcc zero acc L.[] _ = sym (LP.++-identityʳ (toBits acc))
toBits-fromBitsAcc (suc m) acc
  (b₀ L.∷ b₁ L.∷ b₂ L.∷ b₃ L.∷ b₄ L.∷ b₅ L.∷ b₆ L.∷ b₇ L.∷ rest) len = begin
  toBits (fromBitsAcc (x ∷ acc) rest)
  ≡⟨ toBits-fromBitsAcc m (x ∷ acc) rest (ℕP.+-cancelˡ-≡ 8 _ _ len) ⟩
  toBits (x ∷ acc) L.++ rest
  ≡⟨ cong (L._++ rest) (toBits-∷ x acc) ⟩
  (toBits acc L.++ byteBits x) L.++ rest
  ≡⟨ LP.++-assoc (toBits acc) (byteBits x) rest ⟩
  toBits acc L.++ (b₀ L.∷ b₁ L.∷ b₂ L.∷ b₃ L.∷ b₄ L.∷ b₅ L.∷ b₆ L.∷ b₇ L.∷ rest)
  ∎
  where x = bitsToByte (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ [])
toBits-fromBitsAcc (suc m) acc L.[] ()
toBits-fromBitsAcc (suc m) acc (_ L.∷ L.[]) ()
toBits-fromBitsAcc (suc m) acc (_ L.∷ _ L.∷ L.[]) ()
toBits-fromBitsAcc (suc m) acc (_ L.∷ _ L.∷ _ L.∷ L.[]) ()
toBits-fromBitsAcc (suc m) acc (_ L.∷ _ L.∷ _ L.∷ _ L.∷ L.[]) ()
toBits-fromBitsAcc (suc m) acc (_ L.∷ _ L.∷ _ L.∷ _ L.∷ _ L.∷ L.[]) ()
toBits-fromBitsAcc (suc m) acc (_ L.∷ _ L.∷ _ L.∷ _ L.∷ _ L.∷ _ L.∷ L.[]) ()
toBits-fromBitsAcc (suc m) acc (_ L.∷ _ L.∷ _ L.∷ _ L.∷ _ L.∷ _ L.∷ _ L.∷ L.[]) ()

toBits-fromBits : ∀ m bits → L.length bits ≡ m * 8 → toBits (fromBits bits) ≡ bits
toBits-fromBits m bits len = toBits-fromBitsAcc m [] bits len

lengthℕ-fromBits : ∀ m bits → L.length bits ≡ m * 8 → lengthℕ (fromBits bits) ≡ m
lengthℕ-fromBits m bits len = ℕP.*-cancelʳ-≡ _ _ 8 (begin
  lengthℕ (fromBits bits) * 8
  ≡⟨ length-toBits (fromBits bits) ⟨
  L.length (toBits (fromBits bits))
  ≡⟨ cong L.length (toBits-fromBits m bits len) ⟩
  L.length bits
  ≡⟨ len ⟩
  m * 8
  ∎)
```

The typical use: an operation that rearranges the bits of a bytestring
without changing their number produces a bytestring whose bit view is the
rearranged bits.

```
toBits-fromBits-length
  : ∀ bs bits → L.length bits ≡ L.length (toBits bs) → toBits (fromBits bits) ≡ bits
toBits-fromBits-length bs bits len =
  toBits-fromBits (lengthℕ bs) bits (trans len (length-toBits bs))

lengthℕ-fromBits-length
  : ∀ bs bits → L.length bits ≡ L.length (toBits bs) → lengthℕ (fromBits bits) ≡ lengthℕ bs
lengthℕ-fromBits-length bs bits len =
  lengthℕ-fromBits (lengthℕ bs) bits (trans len (length-toBits bs))
```

The bit view of a replicated byte, and of zero bytes in particular.

```
toBits-replicateBS : ∀ n x → toBits (replicateBS n x) ≡ L.concat (L.replicate n (byteBits x))
toBits-replicateBS zero x = refl
toBits-replicateBS (suc n) x = begin
  toBits (x ∷ replicateBS n x)
  ≡⟨ toBits-∷ x (replicateBS n x) ⟩
  toBits (replicateBS n x) L.++ byteBits x
  ≡⟨ cong (L._++ byteBits x) (toBits-replicateBS n x) ⟩
  L.concat (L.replicate n (byteBits x)) L.++ byteBits x
  ≡⟨ concat-replicate-snoc n (byteBits x) ⟩
  L.concat (L.replicate (suc n) (byteBits x))
  ∎
  where
    concat-replicate-snoc
      : ∀ {A : Set} n (xs : L.List A)
      → L.concat (L.replicate n xs) L.++ xs ≡ xs L.++ L.concat (L.replicate n xs)
    concat-replicate-snoc zero xs = sym (LP.++-identityʳ xs)
    concat-replicate-snoc (suc n) xs = begin
      (xs L.++ L.concat (L.replicate n xs)) L.++ xs
      ≡⟨ LP.++-assoc xs _ xs ⟩
      xs L.++ (L.concat (L.replicate n xs) L.++ xs)
      ≡⟨ cong (xs L.++_) (concat-replicate-snoc n xs) ⟩
      xs L.++ (xs L.++ L.concat (L.replicate n xs))
      ∎

toBits-zeros : ∀ n → toBits (replicateBS n 0B) ≡ L.replicate (n * 8) false
toBits-zeros zero = refl
toBits-zeros (suc n) = begin
  toBits (replicateBS (suc n) 0B)
  ≡⟨ toBits-replicateBS (suc n) 0B ⟩
  L.replicate 8 false L.++ L.concat (L.replicate n (L.replicate 8 false))
  ≡⟨ cong (L.replicate 8 false L.++_) (toBits-replicateBS n 0B) ⟨
  L.replicate 8 false L.++ toBits (replicateBS n 0B)
  ≡⟨ cong (L.replicate 8 false L.++_) (toBits-zeros n) ⟩
  L.replicate 8 false L.++ L.replicate (n * 8) false
  ≡⟨ replicate-++ 8 (n * 8) false ⟩
  L.replicate (suc n * 8) false
  ∎

fromBits-zeros : ∀ n → fromBits (L.replicate (n * 8) false) ≡ replicateBS n 0B
fromBits-zeros n = trans (cong fromBits (sym (toBits-zeros n))) (fromBits-toBits (replicateBS n 0B))
```

## Bit lists and lookups

A list of bits is determined by the results of looking up every index: an
index beyond the end of the list gives `nothing`, so the lookups also
determine the length.

```
lookupBit-ext : ∀ xs ys → (∀ i → lookupBit xs i ≡ lookupBit ys i) → xs ≡ ys
lookupBit-ext L.[] L.[] h = refl
lookupBit-ext L.[] (y L.∷ ys) h with () ← h 0
lookupBit-ext (x L.∷ xs) L.[] h with () ← h 0
lookupBit-ext (x L.∷ xs) (y L.∷ ys) h =
  cong₂ L._∷_ (MP.just-injective (h 0)) (lookupBit-ext xs ys (λ i → h (suc i)))

lookupBit-≥ : ∀ xs i → L.length xs ≤ i → lookupBit xs i ≡ nothing
lookupBit-≥ L.[] i _ = refl
lookupBit-≥ (x L.∷ xs) (suc i) (s≤s len≤i) = lookupBit-≥ xs i len≤i

lookupBit-just-< : ∀ xs i {b} → lookupBit xs i ≡ just b → i < L.length xs
lookupBit-just-< (x L.∷ xs) zero _ = s≤s z≤n
lookupBit-just-< (x L.∷ xs) (suc i) eq = s≤s (lookupBit-just-< xs i eq)

-- To compare two lists of the same length, it suffices to compare the
-- lookups of indices below that length.
lookupBit-ext-<
  : ∀ xs ys → L.length xs ≡ L.length ys
  → (∀ i → i < L.length xs → lookupBit xs i ≡ lookupBit ys i) → xs ≡ ys
lookupBit-ext-< xs ys len h = lookupBit-ext xs ys λ i → lookup-eq i (i ℕ.<? L.length xs)
  where
    open import Relation.Nullary.Decidable using (yes; no)
    lookup-eq : ∀ i → _ → lookupBit xs i ≡ lookupBit ys i
    lookup-eq i (yes i<len) = h i i<len
    lookup-eq i (no i≮len) =
      trans (lookupBit-≥ xs i (ℕP.≮⇒≥ i≮len))
            (sym (lookupBit-≥ ys i (subst (_≤ i) len (ℕP.≮⇒≥ i≮len))))

lookupBit-++ˡ : ∀ xs ys i → i < L.length xs → lookupBit (xs L.++ ys) i ≡ lookupBit xs i
lookupBit-++ˡ (x L.∷ xs) ys zero _ = refl
lookupBit-++ˡ (x L.∷ xs) ys (suc i) (s≤s i<len) = lookupBit-++ˡ xs ys i i<len

lookupBit-++ʳ : ∀ xs ys i → lookupBit (xs L.++ ys) (L.length xs + i) ≡ lookupBit ys i
lookupBit-++ʳ L.[] ys i = refl
lookupBit-++ʳ (x L.∷ xs) ys i = lookupBit-++ʳ xs ys i

lookupBit-++ʳ′
  : ∀ xs ys i → L.length xs ≤ i → lookupBit (xs L.++ ys) i ≡ lookupBit ys (i ∸ L.length xs)
lookupBit-++ʳ′ xs ys i len≤i = begin
  lookupBit (xs L.++ ys) i
  ≡⟨ cong (lookupBit (xs L.++ ys)) (ℕP.m+[n∸m]≡n len≤i) ⟨
  lookupBit (xs L.++ ys) (L.length xs + (i ∸ L.length xs))
  ≡⟨ lookupBit-++ʳ xs ys (i ∸ L.length xs) ⟩
  lookupBit ys (i ∸ L.length xs)
  ∎

lookupBit-take : ∀ k xs i → i < k → lookupBit (L.take k xs) i ≡ lookupBit xs i
lookupBit-take (suc k) L.[] i _ = refl
lookupBit-take (suc k) (x L.∷ xs) zero _ = refl
lookupBit-take (suc k) (x L.∷ xs) (suc i) (s≤s i<k) = lookupBit-take k xs i i<k

lookupBit-drop : ∀ k xs i → lookupBit (L.drop k xs) i ≡ lookupBit xs (k + i)
lookupBit-drop zero xs i = refl
lookupBit-drop (suc k) L.[] i = refl
lookupBit-drop (suc k) (x L.∷ xs) i = lookupBit-drop k xs i

lookupBit-replicate : ∀ n b i → i < n → lookupBit (L.replicate n b) i ≡ just b
lookupBit-replicate (suc n) b zero _ = refl
lookupBit-replicate (suc n) b (suc i) (s≤s i<n) = lookupBit-replicate n b i i<n
```

`setBit` changes one bit and leaves the length and all the other bits alone.

```
length-setBit : ∀ i u xs → L.length (setBit i u xs) ≡ L.length xs
length-setBit i u L.[] = refl
length-setBit zero u (x L.∷ xs) = refl
length-setBit (suc i) u (x L.∷ xs) = cong suc (length-setBit i u xs)

lookupBit-setBit-≡ : ∀ i u xs → i < L.length xs → lookupBit (setBit i u xs) i ≡ just u
lookupBit-setBit-≡ zero u (x L.∷ xs) _ = refl
lookupBit-setBit-≡ (suc i) u (x L.∷ xs) (s≤s i<len) = lookupBit-setBit-≡ i u xs i<len

lookupBit-setBit-≢ : ∀ i j u xs → i ≢ j → lookupBit (setBit i u xs) j ≡ lookupBit xs j
lookupBit-setBit-≢ i j u L.[] _ = refl
lookupBit-setBit-≢ zero zero u (x L.∷ xs) i≢j = contradiction refl i≢j
lookupBit-setBit-≢ zero (suc j) u (x L.∷ xs) _ = refl
lookupBit-setBit-≢ (suc i) zero u (x L.∷ xs) _ = refl
lookupBit-setBit-≢ (suc i) (suc j) u (x L.∷ xs) i≢j =
  lookupBit-setBit-≢ i j u xs (λ i≡j → i≢j (cong suc i≡j))
```

The laws relating reads and writes of single bits.

```
setBit-lookupBit : ∀ i u xs → lookupBit xs i ≡ just u → setBit i u xs ≡ xs
setBit-lookupBit zero u (x L.∷ xs) eq = cong (L._∷ xs) (sym (MP.just-injective eq))
setBit-lookupBit (suc i) u (x L.∷ xs) eq = cong (x L.∷_) (setBit-lookupBit i u xs eq)

setBit-setBit : ∀ i u v xs → setBit i u (setBit i v xs) ≡ setBit i u xs
setBit-setBit i u v L.[] = refl
setBit-setBit zero u v (x L.∷ xs) = refl
setBit-setBit (suc i) u v (x L.∷ xs) = cong (x L.∷_) (setBit-setBit i u v xs)

setBit-comm : ∀ i j u xs → setBit i u (setBit j u xs) ≡ setBit j u (setBit i u xs)
setBit-comm i j u L.[] = refl
setBit-comm zero zero u (x L.∷ xs) = refl
setBit-comm zero (suc j) u (x L.∷ xs) = refl
setBit-comm (suc i) zero u (x L.∷ xs) = refl
setBit-comm (suc i) (suc j) u (x L.∷ xs) = cong (x L.∷_) (setBit-comm i j u xs)
```

## Reading and writing bits

A bit index is valid exactly when it is non-negative and below the bit length.

```
validBitIndex-+ : ∀ bs i → i < lengthℕ bs * 8 → validBitIndex (bitLength bs) (+ i) ≡ true
validBitIndex-+ bs i i<len =
  dec-true (+ i ℤ.<? bitLength bs)
    (ℤP.<-≤-trans (+<+ i<len) (ℤP.≤-reflexive (sym (bitLength-lengthℕ bs))))
```

Reading a bit is looking it up in the bit view: a negative index or one
beyond the end fails, as `lookupBit` does.

```
readBIT-lookupBit : ∀ bs i → readBIT bs (+ i) ≡ lookupBit (toBits bs) i
readBIT-lookupBit bs i with + i ℤ.<? bitLength bs
... | yes _ = refl
... | no i≮len = sym (lookupBit-≥ (toBits bs) i
        (ℕP.≮⇒≥ (λ i<len → i≮len
          (ℤP.<-≤-trans (+<+ (ℕP.<-≤-trans i<len (ℕP.≤-reflexive (length-toBits bs))))
                       (ℤP.≤-reflexive (sym (bitLength-lengthℕ bs)))))))

readBIT-neg : ∀ bs i → readBIT bs -[1+ i ] ≡ nothing
readBIT-neg bs i = refl
```

Writing bits applies `setBit` to the bit view for each index, provided every
index is valid. Since `setBit` keeps the length, the result has the same
length as the input, and its bit view is the updated bit list.

```
setBits : L.List ℤ → Bool → Bits* → Bits*
setBits ixs u bits = L.foldr (λ i → setBit (ℤ.∣ i ∣) u) bits ixs

length-setBits : ∀ ixs u bits → L.length (setBits ixs u bits) ≡ L.length bits
length-setBits L.[] u bits = refl
length-setBits (i L.∷ ixs) u bits =
  trans (length-setBit ℤ.∣ i ∣ u (setBits ixs u bits)) (length-setBits ixs u bits)

writeBITS-valid
  : ∀ bs ixs u → all (validBitIndex (bitLength bs)) ixs ≡ true
  → writeBITS bs ixs u ≡ just (fromBits (setBits ixs u (toBits bs)))
writeBITS-valid bs ixs u valid with all (validBitIndex (bitLength bs)) ixs
writeBITS-valid bs ixs u refl | true = refl

writeBITS-invalid
  : ∀ bs ixs u → all (validBitIndex (bitLength bs)) ixs ≡ false
  → writeBITS bs ixs u ≡ nothing
writeBITS-invalid bs ixs u invalid with all (validBitIndex (bitLength bs)) ixs
writeBITS-invalid bs ixs u refl | false = refl

-- The bytestring produced by writing bits.
written : ByteString → L.List ℤ → Bool → ByteString
written bs ixs u = fromBits (setBits ixs u (toBits bs))

toBits-written : ∀ bs ixs u → toBits (written bs ixs u) ≡ setBits ixs u (toBits bs)
toBits-written bs ixs u =
  toBits-fromBits-length bs (setBits ixs u (toBits bs)) (length-setBits ixs u (toBits bs))

lengthℕ-written : ∀ bs ixs u → lengthℕ (written bs ixs u) ≡ lengthℕ bs
lengthℕ-written bs ixs u =
  lengthℕ-fromBits-length bs (setBits ixs u (toBits bs)) (length-setBits ixs u (toBits bs))

bitLength-written : ∀ bs ixs u → bitLength (written bs ixs u) ≡ bitLength bs
bitLength-written bs ixs u =
  trans (bitLength-lengthℕ (written bs ixs u))
  (trans (cong (λ n → + (n * 8)) (lengthℕ-written bs ixs u)) (sym (bitLength-lengthℕ bs)))
```
