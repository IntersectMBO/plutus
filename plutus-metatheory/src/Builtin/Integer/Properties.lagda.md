---
title: Builtin.Integer.Properties
layout: page
---

This module contains proved properties of the extra functions defined in `Builtin.Integer.Base`.

```
module Builtin.Integer.Properties where
```

## Imports

```
open import Builtin.Integer.Base
open import Data.Integer
import Data.Nat as ℕ
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
import Data.Sign as S
import Data.Sign.Properties as SP
import Data.Nat.Properties as ℕP
open import Data.Integer.Properties
open import Data.Nat.DivMod
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
```

## Properties

```
quotRem-law : (n d : ℤ) .{{_ : NonZero d}} → (quot n d) * d + (rem n d) ≡ n
quotRem-law n d = begin
  quot n d * d + rem n d
  ≡⟨⟩
  ((sign n S.* sign d) ◃ q) * d + (sign n ◃ r)
  ≡⟨ cong (λ z → ((sign n S.* sign d) ◃ q) * z + (sign n ◃ r)) (sym (◃-inverse d)) ⟩
  ((sign n S.* sign d) ◃ q) * (sign d ◃ ∣ d ∣) + (sign n ◃ r)
  ≡⟨ cong (_+ (sign n ◃ r)) (sym (◃-distrib-* (sign n S.* sign d) (sign d) q ∣ d ∣)) ⟩
  (((sign n S.* sign d) S.* sign d) ◃ (q ℕ.* ∣ d ∣)) + (sign n ◃ r)
  ≡⟨ cong (λ s → (s ◃ (q ℕ.* ∣ d ∣)) + (sign n ◃ r)) signs≡ ⟩
  (sign n ◃ (q ℕ.* ∣ d ∣)) + (sign n ◃ r)
  ≡⟨ sym (◃-distrib-+ (sign n) (q ℕ.* ∣ d ∣) r) ⟩
  sign n ◃ (q ℕ.* ∣ d ∣ ℕ.+ r)
  ≡⟨ cong (sign n ◃_) nat-law ⟩
  sign n ◃ ∣ n ∣
  ≡⟨ ◃-inverse n ⟩
  n
  ∎
  where
    q = ∣ n ∣ ℕ./ ∣ d ∣
    r = ∣ n ∣ ℕ.% ∣ d ∣
    signs≡ : (sign n S.* sign d) S.* sign d ≡ sign n
    signs≡ = begin
      (sign n S.* sign d) S.* sign d
      ≡⟨ SP.*-assoc (sign n) (sign d) (sign d) ⟩
      sign n S.* (sign d S.* sign d)
      ≡⟨ cong (sign n S.*_) (SP.s*s≡+ (sign d)) ⟩
      sign n S.* S.+
      ≡⟨ SP.*-identityʳ (sign n) ⟩
      sign n
      ∎
    nat-law : q ℕ.* ∣ d ∣ ℕ.+ r ≡ ∣ n ∣
    nat-law = begin
      q ℕ.* ∣ d ∣ ℕ.+ r
      ≡⟨ ℕP.+-comm (q ℕ.* ∣ d ∣) r ⟩
      r ℕ.+ q ℕ.* ∣ d ∣
      ≡⟨ sym (m≡m%n+[m/n]*n ∣ n ∣ ∣ d ∣) ⟩
      ∣ n ∣
      ∎

-- Rearrangement behind the floored-division fixup:
--   (q - 1) * d + (r + d) ≡ q * d + r
predFixup : (q r d : ℤ) → pred q * d + (r + d) ≡ q * d + r
predFixup q r d = begin
  pred q * d + (r + d)
  ≡⟨ cong (_+ (r + d)) (*-distribʳ-+ d -1ℤ q) ⟩
  (-1ℤ * d + q * d) + (r + d)
  ≡⟨ cong (λ z → (z + q * d) + (r + d)) (-1*i≡-i d) ⟩
  ((- d) + q * d) + (r + d)
  ≡⟨ +-assoc (- d) (q * d) (r + d) ⟩
  (- d) + (q * d + (r + d))
  ≡⟨ cong (λ z → (- d) + z) (sym (+-assoc (q * d) r d)) ⟩
  (- d) + ((q * d + r) + d)
  ≡⟨ cong (λ z → (- d) + z) (+-comm (q * d + r) d) ⟩
  (- d) + (d + (q * d + r))
  ≡⟨ sym (+-assoc (- d) d (q * d + r)) ⟩
  ((- d) + d) + (q * d + r)
  ≡⟨ cong (_+ (q * d + r)) (+-inverseˡ d) ⟩
  +0 + (q * d + r)
  ≡⟨ +-identityˡ (q * d + r) ⟩
  q * d + r
  ∎

-- The fixup preserves the quotient-remainder identity.
divModFixup-law : (q r d : ℤ) → proj₁ (divModFixup q r d) * d + proj₂ (divModFixup q r d) ≡ q * d + r
divModFixup-law q (+ _) (-[1+ _ ]) = predFixup q _ _
divModFixup-law q (-[1+ _ ]) (+ _) = predFixup q _ _
divModFixup-law q (+ _) (+ _) = refl
divModFixup-law q (-[1+ _ ]) (-[1+ _ ]) = refl

divMod-law : (n d : ℤ) .{{_ : NonZero d}} → (div n d) * d + (mod n d) ≡ n
divMod-law n d = begin
  div n d * d + mod n d
  ≡⟨ divModFixup-law (quot n d) (rem n d) d ⟩
  quot n d * d + rem n d
  ≡⟨ quotRem-law n d ⟩
  n
  ∎
```