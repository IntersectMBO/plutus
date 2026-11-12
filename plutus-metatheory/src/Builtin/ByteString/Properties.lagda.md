---
title: Builtin.ByteString.Properties
layout: page
---

```
module Builtin.ByteString.Properties where
```

## Imports

```
open import Builtin.ByteString.Base
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _/_; _%_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.DivMod
  using (m<n*o⇒m/o<n; m%n<n; m≡m%n+[m/n]*n; m*n%n≡0; [m+kn]%n≡m%n; m*n/n≡m; +-distrib-/)
open import Data.Nat.Properties using (*-comm)
open import Data.Vec using ([]; _∷_)
open import Data.Vec.Properties using (≡-dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Nullary.Decidable using (recompute)

import Data.Fin as Fin
import Data.Fin.Properties as Fin
```

## Properties

Helper lemma for bitVal and modulo 2 operation.

```
private
  bitVal-%2 : ∀ k → bitVal (k % 2 ≡ᵇ 1) ≡ k % 2
  bitVal-%2 k with k % 2 | m%n<n k 2
  ... | 0                | _ = refl
  ... | 1                | _ = refl
  ... | suc (suc _) | s≤s (s≤s ())
```

`bitsToNat` is the left inverse of `natToBits`:

```
natToBits-leftInverse : ∀ len k → k < 2 ^ len → bitsToNat (natToBits len k) ≡ k
natToBits-leftInverse zero    zero (s≤s z≤n) = refl
natToBits-leftInverse (suc len) k k<
  rewrite natToBits-leftInverse len (k / 2)
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

natToBits-rightInverse : ∀ len bs → natToBits len (bitsToNat bs) ≡ bs
natToBits-rightInverse zero      []       = refl
natToBits-rightInverse (suc len) (b ∷ bs) =
  cong₂ _∷_ (parity b x)
            (trans (cong (natToBits len) (half b x)) (natToBits-rightInverse len bs))
  where
    x = bitsToNat bs

toBinary : (len k : ℕ) → .(k < 2 ^ len) → BinaryOf k
toBinary len k k< = binary len (natToBits len k) (natToBits-leftInverse len k k<)

finToBinary : (len : ℕ) (i : Fin (2 ^ len)) → BinaryOf (Fin.toℕ i)
finToBinary len i = toBinary len (Fin.toℕ i) (Fin.toℕ<n i)

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
  trans (sym (natToBits-leftInverse len n n<))
        (trans (cong bitsToNat eq) (natToBits-leftInverse len m m<))
```

For a given length, the bits of a `BinaryOf n` are determined by `n`: they are exactly
`natToBits len n`.

```
bits-canonical
  : ∀ {n} (x : BinaryOf n)
  → BinaryOf.bits x ≡ natToBits (BinaryOf.len x) n
bits-canonical {n} (binary l bs p) =
  recompute (≡-dec _≟_ bs (natToBits l n))
            (trans (sym (natToBits-rightInverse l bs)) (cong (natToBits l) p))
```