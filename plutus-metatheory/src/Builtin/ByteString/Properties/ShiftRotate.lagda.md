---
title: Builtin.ByteString.Properties.ShiftRotate
layout: page
---

This module proves the laws of `shiftByteString` and `rotateByteString` from
the second batch of bitwise builtins,
[CIP-123](https://cips.cardano.org/cip/CIP-0123). These are the shift and
rotation properties tested by the Haskell test suite
`Evaluation.Builtins.Bitwise.CIP0123`:

* shifting by zero is the identity, and shifts in the same direction compose
  by adding their amounts;
* shifting by at least the bit length clears every bit (in particular,
  shifting by the smallest `Int`);
* shifting by `n` clears the `n` lowest (for a positive shift) or highest (for
  a negative shift) bits, and on a single byte, shifts agree with the
  arithmetic shifts of Haskell's `Data.Bits`;
* rotating by zero, or by any multiple of the bit length, is the identity,
  rotations compose by adding their amounts, and rotating back undoes a
  rotation;
* rotating by `k` moves bit `i` to bit `(i + k) mod n`, where `n` is the bit
  length; and rotating by the smallest `Int` is rotating by its remainder.

The shift and rotation amounts of the builtins are 64-bit `Int`s in
production, so `shiftBYTESTRING` and `rotateBYTESTRING` fail outside that
range. The laws below therefore assume that every amount involved satisfies
`fitsInt`.

```
module Builtin.ByteString.Properties.ShiftRotate where
```

## Imports

```
open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Unit using (tt)
open import Data.Nat as ℕ
  using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _⊓_; _^_; z≤n; s≤s)
open import Data.Nat.Base using (_%_; _/_)
import Data.Nat.Properties as ℕP
import Data.Nat.DivMod as ℕD
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; +[1+_]; 0ℤ; 1ℤ; +<+; +≤+)
import Data.Integer.Properties as ℤP
open import Data.Integer.DivMod using (_%ℕ_; _/ℕ_; a≡a%ℕn+[a/ℕn]*n; n%ℕd<d)
open import Data.Integer.Solver using (module +-*-Solver)
import Data.List as L
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Builtin.Integer.Base using (mod; modMaybe)
open import Builtin.Integer.Properties
  using (divMod-unique-pos-law; mod-size-pos-law; mod-additive-law; mod-plus-multiple-law; modMaybe-correct)
open import Builtin.ByteString.Byte
open import Builtin.ByteString.Base
open import Builtin.ByteString.Denotation
open import Builtin.ByteString.Properties.Byte
open import Builtin.ByteString.Properties.Base
```

## Booleans and natural numbers

```
private

  T⇒≡true : ∀ {b} → T b → b ≡ true
  T⇒≡true {true} _ = refl

  ≡true⇒T : ∀ {b} → b ≡ true → T b
  ≡true⇒T refl = tt

  ≤ᵇ-true : ∀ {m n} → (m ℕ.≤ᵇ n) ≡ true → m ≤ n
  ≤ᵇ-true {m} {n} eq = ℕP.≤ᵇ⇒≤ m n (≡true⇒T eq)

  ≤ᵇ-false : ∀ {m n} → (m ℕ.≤ᵇ n) ≡ false → n < m
  ≤ᵇ-false eq = ℕP.≰⇒> (λ m≤n → subst T eq (ℕP.≤⇒≤ᵇ m≤n))

  <∸ : ∀ m s {n} → m + s < n → m < n ∸ s
  <∸ m s lt = subst (_< _) (ℕP.m+n∸n≡m m s) (ℕP.∸-monoˡ-< lt (ℕP.m≤n+m s m))

  ∸≤ : ∀ m s n → n ≤ m + s → n ∸ s ≤ m
  ∸≤ m s n n≤ = ℕP.m≤n+o⇒m∸n≤o n s (subst (n ≤_) (ℕP.+-comm m s) n≤)

  ∸< : ∀ m s n → s ≤ n → m < n → n ≤ m + s → m ∸ (n ∸ s) < s
  ∸< m s n s≤n m<n n≤ =
    subst (m ∸ (n ∸ s) <_) (ℕP.m∸[m∸n]≡n s≤n) (ℕP.∸-monoˡ-< m<n (∸≤ m s n n≤))
```

## Amounts that fit in an Int

The amounts accepted by the builtins: between `-2⁶³` and `2⁶³ - 1`.

```
fitsInt-pos : ∀ k → k ≤ 9223372036854775807 → fitsInt (+ k) ≡ true
fitsInt-pos k k≤ rewrite T⇒≡true (ℕP.≤⇒≤ᵇ k≤) = refl

fitsInt-neg : ∀ k → k ≤ 9223372036854775808 → fitsInt (ℤ.- (+ k)) ≡ true
fitsInt-neg zero _ = refl
fitsInt-neg (suc k) (s≤s k≤) rewrite T⇒≡true (ℕP.≤⇒≤ᵇ k≤) = refl
```

## Shifts

`shiftBits` shifts the bit view: by `k ≥ 0` towards higher indices (filling
the `k` lowest bits with zeros), by `-k` towards lower indices (filling the `k`
highest bits with zeros), and it clears everything if `k` is at least the
length. Its effect is described bit by bit.

```
shiftBits-pos-low
  : ∀ k bits m → m < L.length bits → m < k
  → lookupBit (shiftBits (+ k) bits) m ≡ just false
shiftBits-pos-low k bits m m<n m<k with L.length bits ℕ.≤ᵇ k
... | true = lookupBit-replicate (L.length bits) false m m<n
... | false =
  trans (lookupBit-++ˡ (L.replicate k false) (L.take (L.length bits ∸ k) bits) m
           (subst (m <_) (sym (LP.length-replicate k)) m<k))
        (lookupBit-replicate k false m m<k)

shiftBits-pos-high
  : ∀ k bits m → k ≤ m → m < L.length bits
  → lookupBit (shiftBits (+ k) bits) m ≡ lookupBit bits (m ∸ k)
shiftBits-pos-high k bits m k≤m m<n with L.length bits ℕ.≤ᵇ k in eq
... | true = contradiction (ℕP.≤-trans (≤ᵇ-true eq) k≤m) (ℕP.<⇒≱ m<n)
... | false = begin
  lookupBit (L.replicate k false L.++ L.take (L.length bits ∸ k) bits) m
  ≡⟨ lookupBit-++ʳ′ (L.replicate k false) _ m (subst (_≤ m) (sym (LP.length-replicate k)) k≤m) ⟩
  lookupBit (L.take (L.length bits ∸ k) bits) (m ∸ L.length (L.replicate k false))
  ≡⟨ cong (λ j → lookupBit (L.take (L.length bits ∸ k) bits) (m ∸ j)) (LP.length-replicate k) ⟩
  lookupBit (L.take (L.length bits ∸ k) bits) (m ∸ k)
  ≡⟨ lookupBit-take (L.length bits ∸ k) bits (m ∸ k) (ℕP.∸-monoˡ-< m<n k≤m) ⟩
  lookupBit bits (m ∸ k)
  ∎

shiftBits-neg-low
  : ∀ k bits m → m + suc k < L.length bits
  → lookupBit (shiftBits -[1+ k ] bits) m ≡ lookupBit bits (m + suc k)
shiftBits-neg-low k bits m lt with L.length bits ℕ.≤ᵇ suc k in eq
... | true = contradiction (ℕP.≤-trans (≤ᵇ-true eq) (ℕP.m≤n+m (suc k) m)) (ℕP.<⇒≱ lt)
... | false = begin
  lookupBit (L.drop (suc k) bits L.++ L.replicate (suc k) false) m
  ≡⟨ lookupBit-++ˡ (L.drop (suc k) bits) _ m
       (subst (m <_) (sym (LP.length-drop (suc k) bits)) (<∸ m (suc k) lt)) ⟩
  lookupBit (L.drop (suc k) bits) m
  ≡⟨ lookupBit-drop (suc k) bits m ⟩
  lookupBit bits (suc k + m)
  ≡⟨ cong (lookupBit bits) (ℕP.+-comm (suc k) m) ⟩
  lookupBit bits (m + suc k)
  ∎

shiftBits-neg-high
  : ∀ k bits m → m < L.length bits → L.length bits ≤ m + suc k
  → lookupBit (shiftBits -[1+ k ] bits) m ≡ just false
shiftBits-neg-high k bits m m<n n≤ with L.length bits ℕ.≤ᵇ suc k in eq
... | true = lookupBit-replicate (L.length bits) false m m<n
... | false = begin
  lookupBit (L.drop (suc k) bits L.++ L.replicate (suc k) false) m
  ≡⟨ lookupBit-++ʳ′ (L.drop (suc k) bits) _ m
       (subst (_≤ m) (sym (LP.length-drop (suc k) bits)) (∸≤ m (suc k) (L.length bits) n≤)) ⟩
  lookupBit (L.replicate (suc k) false) (m ∸ L.length (L.drop (suc k) bits))
  ≡⟨ cong (λ j → lookupBit (L.replicate (suc k) false) (m ∸ j)) (LP.length-drop (suc k) bits) ⟩
  lookupBit (L.replicate (suc k) false) (m ∸ (L.length bits ∸ suc k))
  ≡⟨ lookupBit-replicate (suc k) false _
       (∸< m (suc k) (L.length bits) (ℕP.<⇒≤ (≤ᵇ-false eq)) m<n n≤) ⟩
  just false
  ∎
```

A shift keeps the number of bits.

```
length-shiftBits : ∀ k bits → L.length (shiftBits k bits) ≡ L.length bits
length-shiftBits (+ k) bits with L.length bits ℕ.≤ᵇ k in eq
... | true = LP.length-replicate (L.length bits)
... | false = begin
  L.length (L.replicate k false L.++ L.take (L.length bits ∸ k) bits)
  ≡⟨ LP.length-++ (L.replicate k false) ⟩
  L.length (L.replicate k false) + L.length (L.take (L.length bits ∸ k) bits)
  ≡⟨ cong₂ _+_ (LP.length-replicate k) (LP.length-take (L.length bits ∸ k) bits) ⟩
  k + ((L.length bits ∸ k) ⊓ L.length bits)
  ≡⟨ cong (ℕ._+_ k) (ℕP.m≤n⇒m⊓n≡m (ℕP.m∸n≤m (L.length bits) k)) ⟩
  k + (L.length bits ∸ k)
  ≡⟨ ℕP.m+[n∸m]≡n (ℕP.<⇒≤ (≤ᵇ-false eq)) ⟩
  L.length bits
  ∎
length-shiftBits -[1+ k ] bits with L.length bits ℕ.≤ᵇ suc k in eq
... | true = LP.length-replicate (L.length bits)
... | false = begin
  L.length (L.drop (suc k) bits L.++ L.replicate (suc k) false)
  ≡⟨ LP.length-++ (L.drop (suc k) bits) ⟩
  L.length (L.drop (suc k) bits) + L.length (L.replicate (suc k) false)
  ≡⟨ cong₂ _+_ (LP.length-drop (suc k) bits) (LP.length-replicate (suc k)) ⟩
  (L.length bits ∸ suc k) + suc k
  ≡⟨ ℕP.m∸n+n≡m (ℕP.<⇒≤ (≤ᵇ-false eq)) ⟩
  L.length bits
  ∎
```

Shifting by zero changes nothing.

```
shiftBits-zero : ∀ bits → shiftBits 0ℤ bits ≡ bits
shiftBits-zero bits = lookupBit-ext-< _ _ (length-shiftBits 0ℤ bits) λ m m<len →
  shiftBits-pos-high 0 bits m z≤n (subst (m <_) (length-shiftBits 0ℤ bits) m<len)
```

A negative shift by `s`, uniformly for `s = 0`.

```
shiftBits-neg-low′
  : ∀ s bits m → m + s < L.length bits
  → lookupBit (shiftBits (ℤ.- (+ s)) bits) m ≡ lookupBit bits (m + s)
shiftBits-neg-low′ zero bits m lt =
  trans (cong (λ bs → lookupBit bs m) (shiftBits-zero bits))
        (cong (lookupBit bits) (sym (ℕP.+-identityʳ m)))
shiftBits-neg-low′ (suc k) bits m lt = shiftBits-neg-low k bits m lt

shiftBits-neg-high′
  : ∀ s bits m → m < L.length bits → L.length bits ≤ m + s
  → lookupBit (shiftBits (ℤ.- (+ s)) bits) m ≡ just false
shiftBits-neg-high′ zero bits m m<n n≤ =
  contradiction (subst (L.length bits ≤_) (ℕP.+-identityʳ m) n≤) (ℕP.<⇒≱ m<n)
shiftBits-neg-high′ (suc k) bits m m<n n≤ = shiftBits-neg-high k bits m m<n n≤
```

Shifts in the same direction compose, adding their amounts.

```
shiftBits-+-pos : ∀ i j bits → shiftBits (+ j) (shiftBits (+ i) bits) ≡ shiftBits (+ (i + j)) bits
shiftBits-+-pos i j bits =
  lookupBit-ext-< _ _
    (trans (length-shiftBits (+ j) inner)
           (trans (length-shiftBits (+ i) bits) (sym (length-shiftBits (+ (i + j)) bits))))
    pointwise
  where
    inner = shiftBits (+ i) bits

    pointwise : ∀ m → m < L.length (shiftBits (+ j) inner)
              → lookupBit (shiftBits (+ j) inner) m ≡ lookupBit (shiftBits (+ (i + j)) bits) m
    pointwise m m<len with m ℕ.<? j
    ... | yes m<j =
      let m<inner = subst (m <_) (length-shiftBits (+ j) inner) m<len
          m<n = subst (m <_) (length-shiftBits (+ i) bits) m<inner
      in trans (shiftBits-pos-low j inner m m<inner m<j)
               (sym (shiftBits-pos-low (i + j) bits m m<n (ℕP.<-≤-trans m<j (ℕP.m≤n+m j i))))
    ... | no m≮j with (m ∸ j) ℕ.<? i
    ...   | yes lt =
      let m<inner = subst (m <_) (length-shiftBits (+ j) inner) m<len
          m<n = subst (m <_) (length-shiftBits (+ i) bits) m<inner
          j≤m = ℕP.≮⇒≥ m≮j
      in trans (shiftBits-pos-high j inner m j≤m m<inner)
         (trans (shiftBits-pos-low i bits (m ∸ j) (ℕP.≤-<-trans (ℕP.m∸n≤m m j) m<n) lt)
                (sym (shiftBits-pos-low (i + j) bits m m<n
                       (subst (_< i + j) (ℕP.m∸n+n≡m j≤m) (ℕP.+-monoˡ-< j lt)))))
    ...   | no ge =
      let m<inner = subst (m <_) (length-shiftBits (+ j) inner) m<len
          m<n = subst (m <_) (length-shiftBits (+ i) bits) m<inner
          j≤m = ℕP.≮⇒≥ m≮j
          i≤ = ℕP.≮⇒≥ ge
      in trans (shiftBits-pos-high j inner m j≤m m<inner)
         (trans (shiftBits-pos-high i bits (m ∸ j) i≤ (ℕP.≤-<-trans (ℕP.m∸n≤m m j) m<n))
         (trans (cong (lookupBit bits) (trans (ℕP.∸-+-assoc m j i) (cong (m ∸_) (ℕP.+-comm j i))))
                (sym (shiftBits-pos-high (i + j) bits m
                       (subst (i + j ≤_) (ℕP.m∸n+n≡m j≤m) (ℕP.+-monoˡ-≤ j i≤)) m<n))))

shiftBits-+-neg
  : ∀ i j bits → shiftBits (ℤ.- (+ j)) (shiftBits (ℤ.- (+ i)) bits) ≡ shiftBits (ℤ.- (+ (i + j))) bits
shiftBits-+-neg i j bits =
  lookupBit-ext-< _ _
    (trans (length-shiftBits (ℤ.- (+ j)) inner)
           (trans (length-shiftBits (ℤ.- (+ i)) bits) (sym (length-shiftBits (ℤ.- (+ (i + j))) bits))))
    pointwise
  where
    inner = shiftBits (ℤ.- (+ i)) bits
    n = L.length bits
    len-inner : L.length inner ≡ n
    len-inner = length-shiftBits (ℤ.- (+ i)) bits

    m+[i+j] : ∀ m → m + j + i ≡ m + (i + j)
    m+[i+j] m = trans (ℕP.+-assoc m j i) (cong (ℕ._+_ m) (ℕP.+-comm j i))

    pointwise : ∀ m → m < L.length (shiftBits (ℤ.- (+ j)) inner)
              → lookupBit (shiftBits (ℤ.- (+ j)) inner) m ≡ lookupBit (shiftBits (ℤ.- (+ (i + j))) bits) m
    pointwise m m<len with (m + j) ℕ.<? n
    ... | no m+j≮n =
      let m<inner = subst (m <_) (length-shiftBits (ℤ.- (+ j)) inner) m<len
          m<n = subst (m <_) len-inner m<inner
          n≤ = ℕP.≮⇒≥ m+j≮n
      in trans (shiftBits-neg-high′ j inner m m<inner (subst (_≤ m + j) (sym len-inner) n≤))
               (sym (shiftBits-neg-high′ (i + j) bits m m<n
                      (ℕP.≤-trans n≤ (ℕP.+-monoʳ-≤ m (ℕP.m≤n+m j i)))))
    ... | yes m+j<n with (m + j + i) ℕ.<? n
    ...   | yes lt =
      trans (shiftBits-neg-low′ j inner m (subst (m + j <_) (sym len-inner) m+j<n))
      (trans (shiftBits-neg-low′ i bits (m + j) lt)
      (trans (cong (lookupBit bits) (m+[i+j] m))
             (sym (shiftBits-neg-low′ (i + j) bits m (subst (_< n) (m+[i+j] m) lt)))))
    ...   | no ge =
      let m<inner = subst (m <_) (length-shiftBits (ℤ.- (+ j)) inner) m<len
          m<n = subst (m <_) len-inner m<inner
      in trans (shiftBits-neg-low′ j inner m (subst (m + j <_) (sym len-inner) m+j<n))
         (trans (shiftBits-neg-high′ i bits (m + j) m+j<n (ℕP.≮⇒≥ ge))
                (sym (shiftBits-neg-high′ (i + j) bits m m<n
                       (subst (n ≤_) (m+[i+j] m) (ℕP.≮⇒≥ ge)))))
```

Shifting by at least the length clears every bit.

```
shiftBits-clear : ∀ k bits → L.length bits ≤ ℤ.∣ k ∣ → shiftBits k bits ≡ L.replicate (L.length bits) false
shiftBits-clear k bits h rewrite T⇒≡true (ℕP.≤⇒≤ᵇ h) = refl
```

### The shiftByteString builtin

```
shifted : ByteString → ℤ → ByteString
shifted bs k = fromBits (shiftBits k (toBits bs))

shiftBYTESTRING-fits : ∀ bs k → fitsInt k ≡ true → shiftBYTESTRING bs k ≡ just (shifted bs k)
shiftBYTESTRING-fits bs k fits rewrite fits = refl

toBits-shifted : ∀ bs k → toBits (shifted bs k) ≡ shiftBits k (toBits bs)
toBits-shifted bs k = toBits-fromBits-length bs (shiftBits k (toBits bs)) (length-shiftBits k (toBits bs))
```

Shifting by zero is the identity.

```
shift-zero : ∀ bs → shiftBYTESTRING bs 0ℤ ≡ just bs
shift-zero bs = cong just (trans (cong fromBits (shiftBits-zero (toBits bs))) (fromBits-toBits bs))
```

Shifts in the same direction compose: non-negative shifts form a monoid
homomorphism from addition to composition, and so do non-positive ones.

```
shift-+-pos
  : ∀ bs i j → fitsInt (+ i) ≡ true → fitsInt (+ j) ≡ true → fitsInt (+ (i + j)) ≡ true
  → (shiftBYTESTRING bs (+ i) >>= λ bs' → shiftBYTESTRING bs' (+ j)) ≡ shiftBYTESTRING bs (+ (i + j))
shift-+-pos bs i j fi fj fij
  rewrite shiftBYTESTRING-fits bs (+ i) fi
        | shiftBYTESTRING-fits (shifted bs (+ i)) (+ j) fj
        | shiftBYTESTRING-fits bs (+ (i + j)) fij
  = cong (λ bits → just (fromBits bits))
      (trans (cong (shiftBits (+ j)) (toBits-shifted bs (+ i))) (shiftBits-+-pos i j (toBits bs)))

shift-+-neg
  : ∀ bs i j → fitsInt (ℤ.- (+ i)) ≡ true → fitsInt (ℤ.- (+ j)) ≡ true → fitsInt (ℤ.- (+ (i + j))) ≡ true
  → (shiftBYTESTRING bs (ℤ.- (+ i)) >>= λ bs' → shiftBYTESTRING bs' (ℤ.- (+ j)))
    ≡ shiftBYTESTRING bs (ℤ.- (+ (i + j)))
shift-+-neg bs i j fi fj fij
  rewrite shiftBYTESTRING-fits bs (ℤ.- (+ i)) fi
        | shiftBYTESTRING-fits (shifted bs (ℤ.- (+ i))) (ℤ.- (+ j)) fj
        | shiftBYTESTRING-fits bs (ℤ.- (+ (i + j))) fij
  = cong (λ bits → just (fromBits bits))
      (trans (cong (shiftBits (ℤ.- (+ j))) (toBits-shifted bs (ℤ.- (+ i)))) (shiftBits-+-neg i j (toBits bs)))
```

Shifting by at least the bit length, in either direction, clears the
bytestring. In particular, so does shifting by the smallest `Int`, `-2⁶³`, for
any bytestring of fewer than `2⁶⁰` bytes.

```
shift-clear
  : ∀ bs k → fitsInt k ≡ true → lengthℕ bs * 8 ≤ ℤ.∣ k ∣
  → shiftBYTESTRING bs k ≡ just (replicateBS (lengthℕ bs) 0B)
shift-clear bs k fits h =
  trans (shiftBYTESTRING-fits bs k fits)
    (cong just (trans (cong fromBits
      (trans (shiftBits-clear k (toBits bs) (subst (_≤ ℤ.∣ k ∣) (sym (length-toBits bs)) h))
             (cong (λ n → L.replicate n false) (length-toBits bs))))
      (fromBits-zeros (lengthℕ bs))))

shift-minBound
  : ∀ bs → lengthℕ bs * 8 ≤ 9223372036854775808
  → shiftBYTESTRING bs -[1+ 9223372036854775807 ] ≡ just (replicateBS (lengthℕ bs) 0B)
shift-minBound bs h = shift-clear bs -[1+ 9223372036854775807 ] refl h
```

A positive shift by `n` clears the `n` lowest bits; a negative shift by `n`
clears the `n` highest bits.

```
shift-pos-clear-low
  : ∀ bs n i → fitsInt (+ n) ≡ true → i < n → i < lengthℕ bs * 8
  → (shiftBYTESTRING bs (+ n) >>= λ bs' → readBIT bs' (+ i)) ≡ just false
shift-pos-clear-low bs n i fits i<n i<len
  rewrite shiftBYTESTRING-fits bs (+ n) fits
  = trans (readBIT-lookupBit (shifted bs (+ n)) i)
    (trans (cong (λ bits → lookupBit bits i) (toBits-shifted bs (+ n)))
           (shiftBits-pos-low n (toBits bs) i (subst (i <_) (sym (length-toBits bs)) i<len) i<n))

shift-neg-clear-high
  : ∀ bs n i → fitsInt (ℤ.- (+ n)) ≡ true → i < n → i < lengthℕ bs * 8
  → (shiftBYTESTRING bs (ℤ.- (+ n)) >>= λ bs' → readBIT bs' (+ (lengthℕ bs * 8 ∸ suc i))) ≡ just false
shift-neg-clear-high bs n i fits i<n i<len
  rewrite shiftBYTESTRING-fits bs (ℤ.- (+ n)) fits
  = trans (readBIT-lookupBit (shifted bs (ℤ.- (+ n))) m)
    (trans (cong (λ bits → lookupBit bits m) (toBits-shifted bs (ℤ.- (+ n))))
           (shiftBits-neg-high′ n (toBits bs) m
              (subst (m <_) (sym (length-toBits bs)) m<len)
              (subst (_≤ m + n) (sym (length-toBits bs)) len≤)))
  where
    len = lengthℕ bs * 8
    m = len ∸ suc i
    m<len : m < len
    m<len = ℕP.∸-monoʳ-< (s≤s z≤n) i<len
    len≤ : len ≤ m + n
    len≤ = ℕP.≤-trans (ℕP.≤-reflexive (sym (ℕP.m∸n+n≡m i<len))) (ℕP.+-monoʳ-≤ m i<n)
```

### Shifting a single byte

On a single byte, shifting by `n` between 1 and 7 agrees with the arithmetic
shifts `shiftL` and `shiftR` of Haskell's `Data.Bits` on `Word8`, i.e.
multiplying by `2ⁿ` modulo 256, and dividing by `2ⁿ`. There are only 256
bytes and 7 amounts in each direction, so these are checked by evaluation
(see `allBytes` in `Builtin.ByteString.Properties.Byte`).

```
2^n-nonZero : ∀ n → ℕ.NonZero (2 ^ n)
2^n-nonZero n = ℕ.>-nonZero (ℕP.m^n>0 2 n)

private

  -- Does a computation produce a single byte satisfying p?
  singleton? : (Byte → Bool) → Maybe ByteString → Bool
  singleton? p (just (x ∷ [])) = p x
  singleton? p _ = false

  singleton?-sound
    : ∀ p m → singleton? p m ≡ true → Σ Byte (λ x → (m ≡ just (x ∷ [])) × (p x ≡ true))
  singleton?-sound p (just (x ∷ [])) h = x , refl , h

  shift-check : ℤ → (ℕ → ℕ) → Byte → Bool
  shift-check k f b = singleton? (λ x → byteToℕ x ℕ.≡ᵇ f (byteToℕ b)) (shiftBYTESTRING (b ∷ []) k)

  shift-check-sound
    : ∀ k f b → shift-check k f b ≡ true
    → shiftBYTESTRING (b ∷ []) k ≡ just (ℕToByte (f (byteToℕ b)) ∷ [])
  shift-check-sound k f b h with singleton?-sound _ _ h
  ... | x , eq , px =
    trans eq (cong (λ y → just (y ∷ []))
      (trans (sym (ℕToByte-byteToℕ x)) (cong ℕToByte (ℕP.≡ᵇ⇒≡ (byteToℕ x) (f (byteToℕ b)) (≡true⇒T px)))))

  shiftL : ℕ → ℕ → ℕ
  shiftL n v = (v * 2 ^ n) % 256

  shiftR : ℕ → ℕ → ℕ
  shiftR n v = (v / 2 ^ n) {{2^n-nonZero n}}

  all-shiftL : ∀ n → 0 < n → n < 8 → allBytes (shift-check (+ n) (shiftL n)) ≡ true
  all-shiftL 1 _ _ = refl
  all-shiftL 2 _ _ = refl
  all-shiftL 3 _ _ = refl
  all-shiftL 4 _ _ = refl
  all-shiftL 5 _ _ = refl
  all-shiftL 6 _ _ = refl
  all-shiftL 7 _ _ = refl
  all-shiftL (suc (suc (suc (suc (suc (suc (suc (suc _)))))))) _
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))

  all-shiftR : ∀ n → 0 < n → n < 8 → allBytes (shift-check (ℤ.- (+ n)) (shiftR n)) ≡ true
  all-shiftR 1 _ _ = refl
  all-shiftR 2 _ _ = refl
  all-shiftR 3 _ _ = refl
  all-shiftR 4 _ _ = refl
  all-shiftR 5 _ _ = refl
  all-shiftR 6 _ _ = refl
  all-shiftR 7 _ _ = refl
  all-shiftR (suc (suc (suc (suc (suc (suc (suc (suc _)))))))) _
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))

shift-byte-pos
  : ∀ b n → 0 < n → n < 8
  → shiftBYTESTRING (b ∷ []) (+ n) ≡ just (ℕToByte ((byteToℕ b * 2 ^ n) % 256) ∷ [])
shift-byte-pos b n 0<n n<8 =
  shift-check-sound (+ n) (shiftL n) b (allBytes-sound (shift-check (+ n) (shiftL n)) (all-shiftL n 0<n n<8) b)

shift-byte-neg
  : ∀ b n → 0 < n → n < 8
  → shiftBYTESTRING (b ∷ []) (ℤ.- (+ n)) ≡ just (ℕToByte ((byteToℕ b / 2 ^ n) {{2^n-nonZero n}}) ∷ [])
shift-byte-neg b n 0<n n<8 =
  shift-check-sound (ℤ.- (+ n)) (shiftR n) b (allBytes-sound (shift-check (ℤ.- (+ n)) (shiftR n)) (all-shiftR n 0<n n<8) b)
```

## Rotations

`rotateBits k` rotates the bit view by `k` places towards higher indices: the
bit at index `m` of the result is the bit at index `(m - k) mod n` of the
input, where `n` is the length. The definition computes the remainder with the
standard library's `_%ℕ_`; the statement uses `mod` from
`Builtin.Integer.Base` (Haskell's `mod`, the denotation of `modInteger`), so
that the laws of `Builtin.Integer.Properties` apply. For a positive divisor the
two agree.

```
%ℕ-mod : ∀ a n → + (a %ℕ suc n) ≡ mod a +[1+ n ]
%ℕ-mod a n =
  proj₂ (divMod-unique-pos-law a (a /ℕ suc n) (+ (a %ℕ suc n)) +[1+ n ]
          (+≤+ z≤n) (+<+ (n%ℕd<d a (suc n)))
          (trans (a≡a%ℕn+[a/ℕn]*n a (suc n)) (ℤP.+-comm (+ (a %ℕ suc n)) ((a /ℕ suc n) ℤ.* +[1+ n ]))))
```

Some consequences of the `mod` laws, for a positive divisor.

```
private

  mod-small : ∀ x n → 0ℤ ℤ.≤ x → x ℤ.< +[1+ n ] → mod x +[1+ n ] ≡ x
  mod-small x n 0≤x x< =
    sym (proj₂ (divMod-unique-pos-law x 0ℤ x +[1+ n ] 0≤x x< (sym (ℤP.+-identityˡ x))))

  mod-mod : ∀ x n → mod (mod x +[1+ n ]) +[1+ n ] ≡ mod x +[1+ n ]
  mod-mod x n = mod-small (mod x +[1+ n ]) n
    (proj₁ (mod-size-pos-law x +[1+ n ])) (proj₂ (mod-size-pos-law x +[1+ n ]))

  +∣mod∣ : ∀ x n → + ℤ.∣ mod x +[1+ n ] ∣ ≡ mod x +[1+ n ]
  +∣mod∣ x n = ℤP.0≤i⇒+∣i∣≡i (proj₁ (mod-size-pos-law x +[1+ n ]))

  ∣mod∣< : ∀ x n → ℤ.∣ mod x +[1+ n ] ∣ < suc n
  ∣mod∣< x n = ℤP.drop‿+<+ (subst (ℤ._< +[1+ n ]) (sym (+∣mod∣ x n)) (proj₂ (mod-size-pos-law x +[1+ n ])))

  mod-sub-mod : ∀ a i n → mod (mod a +[1+ n ] ℤ.- i) +[1+ n ] ≡ mod (a ℤ.- i) +[1+ n ]
  mod-sub-mod a i n = begin
    mod (mod a N ℤ.+ ℤ.- i) N
    ≡⟨ mod-additive-law (mod a N) (ℤ.- i) N ⟩
    mod (mod (mod a N) N ℤ.+ mod (ℤ.- i) N) N
    ≡⟨ cong (λ z → mod (z ℤ.+ mod (ℤ.- i) N) N) (mod-mod a n) ⟩
    mod (mod a N ℤ.+ mod (ℤ.- i) N) N
    ≡⟨ mod-additive-law a (ℤ.- i) N ⟨
    mod (a ℤ.+ ℤ.- i) N
    ∎
    where N = +[1+ n ]

  open +-*-Solver

  ring₁ : ∀ m d r q → (m ℤ.+ d) ℤ.+ ℤ.- (q ℤ.+ 1ℤ) ℤ.* (d ℤ.+ r) ≡ m ℤ.- (r ℤ.+ q ℤ.* (d ℤ.+ r))
  ring₁ = solve 4 (λ m d r q → (m :+ d) :+ (:- (q :+ con 1ℤ)) :* (d :+ r) := m :- (r :+ q :* (d :+ r))) refl

  ring₂ : ∀ m i j → (m ℤ.- j) ℤ.- i ≡ m ℤ.- (i ℤ.+ j)
  ring₂ = solve 3 (λ m i j → (m :- j) :- i := m :- (i :+ j)) refl

  ring₃ : ∀ m k c n → m ℤ.- (k ℤ.+ c ℤ.* n) ≡ (m ℤ.- k) ℤ.+ ℤ.- c ℤ.* n
  ring₃ = solve 4 (λ m k c n → m :- (k :+ c :* n) := (m :- k) :+ (:- c) :* n) refl

  ring₄ : ∀ i j → (i ℤ.+ j) ℤ.- j ≡ i
  ring₄ = solve 2 (λ i j → (i :+ j) :- j := i) refl
```

The bit at index `m` of the rotation is found, in the naturals, by the
remainder of `m + (n - r)`, where `r` is the rotation amount reduced modulo
`n`.

```
private

  rot-index
    : ∀ bits r m .{{_ : ℕ.NonZero (L.length bits)}} → r < L.length bits → m < L.length bits
    → lookupBit (L.drop (L.length bits ∸ r) bits L.++ L.take (L.length bits ∸ r) bits) m
      ≡ lookupBit bits ((m + (L.length bits ∸ r)) % L.length bits)
  rot-index bits r m r<n m<n with m ℕ.<? r
  ... | yes m<r = begin
    lookupBit (L.drop d bits L.++ L.take d bits) m
    ≡⟨ lookupBit-++ˡ (L.drop d bits) _ m (subst (m <_) (sym len-drop) m<r) ⟩
    lookupBit (L.drop d bits) m
    ≡⟨ lookupBit-drop d bits m ⟩
    lookupBit bits (d + m)
    ≡⟨ cong (lookupBit bits) (trans (ℕP.+-comm d m) (sym (ℕD.m<n⇒m%n≡m m+d<n))) ⟩
    lookupBit bits ((m + d) % n)
    ∎
    where
      n = L.length bits
      d = n ∸ r
      len-drop : L.length (L.drop d bits) ≡ r
      len-drop = trans (LP.length-drop d bits) (ℕP.m∸[m∸n]≡n (ℕP.<⇒≤ r<n))
      m+d<n : m + d < n
      m+d<n = subst (m + d <_) (ℕP.m+[n∸m]≡n (ℕP.<⇒≤ r<n)) (ℕP.+-monoˡ-< d m<r)
  ... | no m≮r = begin
    lookupBit (L.drop d bits L.++ L.take d bits) m
    ≡⟨ lookupBit-++ʳ′ (L.drop d bits) _ m (subst (_≤ m) (sym len-drop) r≤m) ⟩
    lookupBit (L.take d bits) (m ∸ L.length (L.drop d bits))
    ≡⟨ cong (λ j → lookupBit (L.take d bits) (m ∸ j)) len-drop ⟩
    lookupBit (L.take d bits) (m ∸ r)
    ≡⟨ lookupBit-take d bits (m ∸ r) (ℕP.∸-monoˡ-< m<n r≤m) ⟩
    lookupBit bits (m ∸ r)
    ≡⟨ cong (lookupBit bits) (sym idx) ⟩
    lookupBit bits ((m + d) % n)
    ∎
    where
      n = L.length bits
      d = n ∸ r
      r≤m = ℕP.≮⇒≥ m≮r
      len-drop : L.length (L.drop d bits) ≡ r
      len-drop = trans (LP.length-drop d bits) (ℕP.m∸[m∸n]≡n (ℕP.<⇒≤ r<n))
      m+d≡ : m + d ≡ (m ∸ r) + n
      m+d≡ = trans (sym (ℕP.+-∸-assoc m (ℕP.<⇒≤ r<n))) (ℕP.+-∸-comm n r≤m)
      idx : (m + d) % n ≡ m ∸ r
      idx = trans (cong (_% n) m+d≡)
            (trans (ℕD.[m+n]%n≡m%n (m ∸ r) n)
                   (ℕD.m<n⇒m%n≡m (ℕP.≤-<-trans (ℕP.m∸n≤m m r) m<n)))
```

In the integers, that index is `(m - k) mod n`.

```
private

  rot-offset : ∀ m k n → + ((m + (suc n ∸ k %ℕ suc n)) % suc n) ≡ mod (+ m ℤ.- k) +[1+ n ]
  rot-offset m k n = begin
    + ((m + d) % N)
    ≡⟨ %ℕ-mod (+ (m + d)) n ⟩
    mod (+ (m + d)) +[1+ n ]
    ≡⟨ mod-plus-multiple-law (+ (m + d)) c +[1+ n ] ⟨
    mod (+ (m + d) ℤ.+ c ℤ.* + N) +[1+ n ]
    ≡⟨ cong (λ z → mod z +[1+ n ]) arith ⟩
    mod (+ m ℤ.- k) +[1+ n ]
    ∎
    where
      N = suc n
      r = k %ℕ N
      q = k /ℕ N
      d = N ∸ r
      c = ℤ.- (q ℤ.+ 1ℤ)
      N≡ : + N ≡ + d ℤ.+ + r
      N≡ = trans (cong +_ (sym (ℕP.m∸n+n≡m (ℕP.<⇒≤ (n%ℕd<d k N))))) (ℤP.pos-+ d r)
      arith : + (m + d) ℤ.+ c ℤ.* + N ≡ + m ℤ.- k
      arith = begin
        + (m + d) ℤ.+ c ℤ.* + N
        ≡⟨ cong₂ (λ x y → x ℤ.+ c ℤ.* y) (ℤP.pos-+ m d) N≡ ⟩
        (+ m ℤ.+ + d) ℤ.+ c ℤ.* (+ d ℤ.+ + r)
        ≡⟨ ring₁ (+ m) (+ d) (+ r) q ⟩
        + m ℤ.- (+ r ℤ.+ q ℤ.* (+ d ℤ.+ + r))
        ≡⟨ cong (λ y → + m ℤ.- (+ r ℤ.+ q ℤ.* y)) N≡ ⟨
        + m ℤ.- (+ r ℤ.+ q ℤ.* + N)
        ≡⟨ cong (λ y → + m ℤ.- y) (a≡a%ℕn+[a/ℕn]*n k N) ⟨
        + m ℤ.- k
        ∎
```

The bit-by-bit description of a rotation, and the fact that rotations keep
the number of bits.

```
rotateBits-lookup
  : ∀ k bits n → L.length bits ≡ suc n → ∀ m → m < suc n
  → lookupBit (rotateBits k bits) m ≡ lookupBit bits ℤ.∣ mod (+ m ℤ.- k) +[1+ n ] ∣
rotateBits-lookup k (x L.∷ xs) n refl m m<n =
  trans (rot-index (x L.∷ xs) (k %ℕ suc n) m (n%ℕd<d k (suc n)) m<n)
        (cong (λ i → lookupBit (x L.∷ xs) ℤ.∣ i ∣) (rot-offset m k n))

length-rotateBits : ∀ k bits → L.length (rotateBits k bits) ≡ L.length bits
length-rotateBits k L.[] = refl
length-rotateBits k (x L.∷ xs) = begin
  L.length (L.drop d bits L.++ L.take d bits)
  ≡⟨ LP.length-++ (L.drop d bits) ⟩
  L.length (L.drop d bits) + L.length (L.take d bits)
  ≡⟨ cong₂ _+_ (LP.length-drop d bits) (LP.length-take d bits) ⟩
  (n ∸ d) + (d ⊓ n)
  ≡⟨ cong (ℕ._+_ (n ∸ d)) (ℕP.m≤n⇒m⊓n≡m (ℕP.m∸n≤m n (k %ℕ n))) ⟩
  (n ∸ d) + d
  ≡⟨ ℕP.m∸n+n≡m (ℕP.m∸n≤m n (k %ℕ n)) ⟩
  n
  ∎
  where
    bits = x L.∷ xs
    n = L.length bits
    d = n ∸ k %ℕ n
```

Rotating by zero, or by a multiple of the length, changes nothing, and
rotations compose by adding their amounts.

```
rotateBits-zero : ∀ bits → rotateBits 0ℤ bits ≡ bits
rotateBits-zero L.[] = refl
rotateBits-zero bits@(x L.∷ xs) =
  lookupBit-ext-< _ _ (length-rotateBits 0ℤ bits) λ m m<len →
    let m<n = subst (m <_) (length-rotateBits 0ℤ bits) m<len in
    trans (rotateBits-lookup 0ℤ bits (L.length xs) refl m m<n)
          (cong (λ i → lookupBit bits ℤ.∣ i ∣)
            (trans (cong (λ z → mod z +[1+ L.length xs ]) (ℤP.+-identityʳ (+ m)))
                   (mod-small (+ m) (L.length xs) (+≤+ z≤n) (+<+ m<n))))

rotateBits-multiple : ∀ k c bits → rotateBits (k ℤ.+ c ℤ.* + L.length bits) bits ≡ rotateBits k bits
rotateBits-multiple k c L.[] = refl
rotateBits-multiple k c bits@(x L.∷ xs) =
  lookupBit-ext-< _ _ (trans (length-rotateBits k′ bits) (sym (length-rotateBits k bits))) λ m m<len →
    let m<n = subst (m <_) (length-rotateBits k′ bits) m<len in
    trans (rotateBits-lookup k′ bits (L.length xs) refl m m<n)
    (trans (cong (λ i → lookupBit bits ℤ.∣ i ∣)
             (trans (cong (λ z → mod z N) (ring₃ (+ m) k c N))
                    (mod-plus-multiple-law (+ m ℤ.- k) (ℤ.- c) N)))
           (sym (rotateBits-lookup k bits (L.length xs) refl m m<n)))
  where
    N = +[1+ L.length xs ]
    k′ = k ℤ.+ c ℤ.* N

rotateBits-+ : ∀ i j bits → rotateBits j (rotateBits i bits) ≡ rotateBits (i ℤ.+ j) bits
rotateBits-+ i j L.[] = refl
rotateBits-+ i j bits@(x L.∷ xs) =
  lookupBit-ext-< _ _
    (trans (length-rotateBits j inner) (trans len-inner (sym (length-rotateBits (i ℤ.+ j) bits))))
    pointwise
  where
    n = L.length xs
    N = +[1+ n ]
    inner = rotateBits i bits
    len-inner : L.length inner ≡ suc n
    len-inner = length-rotateBits i bits

    pointwise : ∀ m → m < L.length (rotateBits j inner)
              → lookupBit (rotateBits j inner) m ≡ lookupBit (rotateBits (i ℤ.+ j) bits) m
    pointwise m m<len = begin
      lookupBit (rotateBits j inner) m
      ≡⟨ rotateBits-lookup j inner n len-inner m m<n ⟩
      lookupBit inner ℤ.∣ mod a N ∣
      ≡⟨ rotateBits-lookup i bits n refl ℤ.∣ mod a N ∣ (∣mod∣< a n) ⟩
      lookupBit bits ℤ.∣ mod (+ ℤ.∣ mod a N ∣ ℤ.- i) N ∣
      ≡⟨ cong (λ z → lookupBit bits ℤ.∣ mod (z ℤ.- i) N ∣) (+∣mod∣ a n) ⟩
      lookupBit bits ℤ.∣ mod (mod a N ℤ.- i) N ∣
      ≡⟨ cong (λ z → lookupBit bits ℤ.∣ z ∣) (mod-sub-mod a i n) ⟩
      lookupBit bits ℤ.∣ mod (a ℤ.- i) N ∣
      ≡⟨ cong (λ z → lookupBit bits ℤ.∣ mod z N ∣) (ring₂ (+ m) i j) ⟩
      lookupBit bits ℤ.∣ mod (+ m ℤ.- (i ℤ.+ j)) N ∣
      ≡⟨ rotateBits-lookup (i ℤ.+ j) bits n refl m m<n ⟨
      lookupBit (rotateBits (i ℤ.+ j) bits) m
      ∎
      where
        a = + m ℤ.- j
        m<n : m < suc n
        m<n = subst (m <_) (trans (length-rotateBits j inner) len-inner) m<len
```

### The rotateByteString builtin

```
rotated : ByteString → ℤ → ByteString
rotated bs k = fromBits (rotateBits k (toBits bs))

rotateBYTESTRING-fits : ∀ bs k → fitsInt k ≡ true → rotateBYTESTRING bs k ≡ just (rotated bs k)
rotateBYTESTRING-fits bs k fits rewrite fits = refl

toBits-rotated : ∀ bs k → toBits (rotated bs k) ≡ rotateBits k (toBits bs)
toBits-rotated bs k = toBits-fromBits-length bs (rotateBits k (toBits bs)) (length-rotateBits k (toBits bs))

private

  bitLength-toBits : ∀ bs → bitLength bs ≡ + L.length (toBits bs)
  bitLength-toBits bs = trans (bitLength-lengthℕ bs) (cong +_ (sym (length-toBits bs)))
```

Rotating by zero is the identity.

```
rotate-zero : ∀ bs → rotateBYTESTRING bs 0ℤ ≡ just bs
rotate-zero bs = cong just (trans (cong fromBits (rotateBits-zero (toBits bs))) (fromBits-toBits bs))
```

Rotations form a monoid homomorphism from addition to composition.

```
rotate-+
  : ∀ bs i j → fitsInt i ≡ true → fitsInt j ≡ true → fitsInt (i ℤ.+ j) ≡ true
  → (rotateBYTESTRING bs i >>= λ bs' → rotateBYTESTRING bs' j) ≡ rotateBYTESTRING bs (i ℤ.+ j)
rotate-+ bs i j fi fj fij
  rewrite rotateBYTESTRING-fits bs i fi
        | rotateBYTESTRING-fits (rotated bs i) j fj
        | rotateBYTESTRING-fits bs (i ℤ.+ j) fij
  = cong (λ bits → just (fromBits bits))
      (trans (cong (rotateBits j) (toBits-rotated bs i)) (rotateBits-+ i j (toBits bs)))
```

Rotating back undoes a rotation.

```
rotate-inverse
  : ∀ bs i → fitsInt i ≡ true → fitsInt (ℤ.- i) ≡ true
  → (rotateBYTESTRING bs i >>= λ bs' → rotateBYTESTRING bs' (ℤ.- i)) ≡ just bs
rotate-inverse bs i fi fni =
  trans (rotate-+ bs i (ℤ.- i) fi fni (cong fitsInt (ℤP.+-inverseʳ i)))
        (trans (cong (rotateBYTESTRING bs) (ℤP.+-inverseʳ i)) (rotate-zero bs))
```

Rotating by an amount that differs by a multiple of the bit length gives the
same result. In particular, rotations by more than the bit length "roll over",
and rotating by a multiple of the bit length is the identity.

```
rotate-multiple
  : ∀ bs k c → fitsInt k ≡ true → fitsInt (k ℤ.+ c ℤ.* bitLength bs) ≡ true
  → rotateBYTESTRING bs (k ℤ.+ c ℤ.* bitLength bs) ≡ rotateBYTESTRING bs k
rotate-multiple bs k c fk fkc
  rewrite rotateBYTESTRING-fits bs (k ℤ.+ c ℤ.* bitLength bs) fkc
        | rotateBYTESTRING-fits bs k fk
        | bitLength-toBits bs
  = cong (λ bits → just (fromBits bits)) (rotateBits-multiple k c (toBits bs))

rotate-rollover⁺
  : ∀ bs k → fitsInt k ≡ true → fitsInt (bitLength bs ℤ.+ k) ≡ true
  → rotateBYTESTRING bs (bitLength bs ℤ.+ k) ≡ rotateBYTESTRING bs k
rotate-rollover⁺ bs k fk fLk =
  trans (cong (rotateBYTESTRING bs) eq)
        (rotate-multiple bs k 1ℤ fk (trans (cong fitsInt (sym eq)) fLk))
  where
    eq : bitLength bs ℤ.+ k ≡ k ℤ.+ 1ℤ ℤ.* bitLength bs
    eq = trans (ℤP.+-comm (bitLength bs) k) (cong (ℤ._+_ k) (sym (ℤP.*-identityˡ (bitLength bs))))

rotate-rollover⁻
  : ∀ bs k → fitsInt k ≡ true → fitsInt (ℤ.- bitLength bs ℤ.+ k) ≡ true
  → rotateBYTESTRING bs (ℤ.- bitLength bs ℤ.+ k) ≡ rotateBYTESTRING bs k
rotate-rollover⁻ bs k fk fLk =
  trans (cong (rotateBYTESTRING bs) eq)
        (rotate-multiple bs k (ℤ.- 1ℤ) fk (trans (cong fitsInt (sym eq)) fLk))
  where
    eq : ℤ.- bitLength bs ℤ.+ k ≡ k ℤ.+ ℤ.- 1ℤ ℤ.* bitLength bs
    eq = trans (ℤP.+-comm (ℤ.- bitLength bs) k)
               (cong (ℤ._+_ k) (trans (cong ℤ.-_ (sym (ℤP.*-identityˡ (bitLength bs))))
                                     (ℤP.neg-distribˡ-* 1ℤ (bitLength bs))))

rotate-identity
  : ∀ bs c → fitsInt (c ℤ.* bitLength bs) ≡ true
  → rotateBYTESTRING bs (c ℤ.* bitLength bs) ≡ just bs
rotate-identity bs c fc =
  trans (cong (rotateBYTESTRING bs) (sym (ℤP.+-identityˡ (c ℤ.* bitLength bs))))
        (trans (rotate-multiple bs 0ℤ c refl (trans (cong fitsInt (ℤP.+-identityˡ (c ℤ.* bitLength bs))) fc))
               (rotate-zero bs))
```

Rotating by the smallest `Int`, `-2⁶³`, is rotating by minus the remainder of
`2⁶³` by the bit length.

```
rotate-minBound
  : ∀ x xs
  → rotateBYTESTRING (x ∷ xs) -[1+ 9223372036854775807 ]
    ≡ rotateBYTESTRING (x ∷ xs) (ℤ.- (+ (9223372036854775808 % (lengthℕ (x ∷ xs) * 8))))
rotate-minBound x xs =
  trans (cong (rotateBYTESTRING bs) minBound≡)
        (rotate-multiple bs (ℤ.- (+ r)) (ℤ.- (+ q))
          (fitsInt-neg r (ℕD.m%n≤m 9223372036854775808 N))
          (trans (cong fitsInt (sym minBound≡)) refl))
  where
    bs = x ∷ xs
    N = lengthℕ bs * 8
    r = 9223372036854775808 % N
    q = 9223372036854775808 / N
    minBound≡ : -[1+ 9223372036854775807 ] ≡ ℤ.- (+ r) ℤ.+ ℤ.- (+ q) ℤ.* bitLength bs
    minBound≡ = begin
      ℤ.- (+ 9223372036854775808)
      ≡⟨ cong (λ n → ℤ.- (+ n)) (ℕD.m≡m%n+[m/n]*n 9223372036854775808 N) ⟩
      ℤ.- (+ (r + q * N))
      ≡⟨ cong ℤ.-_ (trans (ℤP.pos-+ r (q * N)) (cong (ℤ._+_ (+ r)) (ℤP.pos-* q N))) ⟩
      ℤ.- (+ r ℤ.+ + q ℤ.* + N)
      ≡⟨ ℤP.neg-distrib-+ (+ r) (+ q ℤ.* + N) ⟩
      ℤ.- (+ r) ℤ.+ ℤ.- (+ q ℤ.* + N)
      ≡⟨ cong (ℤ._+_ (ℤ.- (+ r))) (ℤP.neg-distribˡ-* (+ q) (+ N)) ⟩
      ℤ.- (+ r) ℤ.+ ℤ.- (+ q) ℤ.* + N
      ≡⟨ cong (λ z → ℤ.- (+ r) ℤ.+ ℤ.- (+ q) ℤ.* z) (bitLength-lengthℕ bs) ⟨
      ℤ.- (+ r) ℤ.+ ℤ.- (+ q) ℤ.* bitLength bs
      ∎
```

Rotations move bits but do not change them: rotating by `j` moves the bit at
index `i` to index `(i + j) mod n`, computed with `modInteger`.

```
rotate-move-bits
  : ∀ bs i j → i < lengthℕ bs * 8 → fitsInt j ≡ true
  → (rotateBYTESTRING bs j >>= λ bs' → modMaybe (+ i ℤ.+ j) (bitLength bs) >>= λ m → readBIT bs' m)
    ≡ readBIT bs (+ i)
rotate-move-bits [] i j () fj
rotate-move-bits (x ∷ xs) i j i<len fj =
  trans (cong (λ L → rotateBYTESTRING (x ∷ xs) j >>= λ bs' → modMaybe (+ i ℤ.+ j) L >>= λ m → readBIT bs' m)
              (bitLength-lengthℕ (x ∷ xs)))
        (rotate-move-bits′ x xs i j i<len fj)
  where
    rotate-move-bits′
      : ∀ x xs i j → i < lengthℕ (x ∷ xs) * 8 → fitsInt j ≡ true
      → (rotateBYTESTRING (x ∷ xs) j >>= λ bs' →
         modMaybe (+ i ℤ.+ j) (+ (lengthℕ (x ∷ xs) * 8)) >>= λ m → readBIT bs' m)
        ≡ readBIT (x ∷ xs) (+ i)
    rotate-move-bits′ x xs i j i<len fj
      rewrite rotateBYTESTRING-fits (x ∷ xs) j fj
            | modMaybe-correct (+ i ℤ.+ j) (+ (lengthℕ (x ∷ xs) * 8)) (λ ())
      = begin
        readBIT (rotated bs j) μ
        ≡⟨ cong (readBIT (rotated bs j)) (+∣mod∣ (+ i ℤ.+ j) n) ⟨
        readBIT (rotated bs j) (+ ℤ.∣ μ ∣)
        ≡⟨ readBIT-lookupBit (rotated bs j) ℤ.∣ μ ∣ ⟩
        lookupBit (toBits (rotated bs j)) ℤ.∣ μ ∣
        ≡⟨ cong (λ bits → lookupBit bits ℤ.∣ μ ∣) (toBits-rotated bs j) ⟩
        lookupBit (rotateBits j (toBits bs)) ℤ.∣ μ ∣
        ≡⟨ rotateBits-lookup j (toBits bs) n (length-toBits bs) ℤ.∣ μ ∣ (∣mod∣< (+ i ℤ.+ j) n) ⟩
        lookupBit (toBits bs) ℤ.∣ mod (+ ℤ.∣ μ ∣ ℤ.- j) N ∣
        ≡⟨ cong (λ z → lookupBit (toBits bs) ℤ.∣ mod (z ℤ.- j) N ∣) (+∣mod∣ (+ i ℤ.+ j) n) ⟩
        lookupBit (toBits bs) ℤ.∣ mod (μ ℤ.- j) N ∣
        ≡⟨ cong (λ z → lookupBit (toBits bs) ℤ.∣ z ∣) (mod-sub-mod (+ i ℤ.+ j) j n) ⟩
        lookupBit (toBits bs) ℤ.∣ mod ((+ i ℤ.+ j) ℤ.- j) N ∣
        ≡⟨ cong (λ z → lookupBit (toBits bs) ℤ.∣ mod z N ∣) (ring₄ (+ i) j) ⟩
        lookupBit (toBits bs) ℤ.∣ mod (+ i) N ∣
        ≡⟨ cong (λ z → lookupBit (toBits bs) ℤ.∣ z ∣) (mod-small (+ i) n (+≤+ z≤n) (+<+ i<len)) ⟩
        lookupBit (toBits bs) i
        ≡⟨ readBIT-lookupBit bs i ⟨
        readBIT bs (+ i)
        ∎
      where
        bs = x ∷ xs
        n = 7 + lengthℕ xs * 8
        N = +[1+ n ]
        μ = mod (+ i ℤ.+ j) N
```
