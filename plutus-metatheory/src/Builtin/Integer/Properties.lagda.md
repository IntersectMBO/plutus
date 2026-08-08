---
title: Builtin.Integer.Properties
layout: page
---

This module contains proved properties of the functions defined in `Builtin.Integer.Base`.

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
open import Level using (0ℓ)
open import Algebra.Bundles.Raw using (RawMonoid)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism)
```

## Properties

```
signs≡ : (n d : ℤ) → (sign n S.* sign d) S.* sign d ≡ sign n
signs≡ n d = begin
  (sign n S.* sign d) S.* sign d
  ≡⟨ SP.*-assoc (sign n) (sign d) (sign d) ⟩
  sign n S.* (sign d S.* sign d)
  ≡⟨ cong (sign n S.*_) (SP.s*s≡+ (sign d)) ⟩
  sign n S.* S.+
  ≡⟨ SP.*-identityʳ (sign n) ⟩
  sign n
  ∎

quotRem-law : (n d : ℤ) .{{_ : NonZero d}} → (quot n d) * d + (rem n d) ≡ n
quotRem-law n d = begin
  quot n d * d + rem n d
  ≡⟨⟩
  ((sign n S.* sign d) ◃ q) * d + (sign n ◃ r)
  ≡⟨ cong (λ z → ((sign n S.* sign d) ◃ q) * z + (sign n ◃ r)) (sym (◃-inverse d)) ⟩
  ((sign n S.* sign d) ◃ q) * (sign d ◃ ∣ d ∣) + (sign n ◃ r)
  ≡⟨ cong (_+ (sign n ◃ r)) (sym (◃-distrib-* (sign n S.* sign d) (sign d) q ∣ d ∣)) ⟩
  (((sign n S.* sign d) S.* sign d) ◃ (q ℕ.* ∣ d ∣)) + (sign n ◃ r)
  ≡⟨ cong (λ s → (s ◃ (q ℕ.* ∣ d ∣)) + (sign n ◃ r)) (signs≡ n d) ⟩
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
    nat-law : q ℕ.* ∣ d ∣ ℕ.+ r ≡ ∣ n ∣
    nat-law = begin
      q ℕ.* ∣ d ∣ ℕ.+ r
      ≡⟨ ℕP.+-comm (q ℕ.* ∣ d ∣) r ⟩
      r ℕ.+ q ℕ.* ∣ d ∣
      ≡⟨ sym (m≡m%n+[m/n]*n ∣ n ∣ ∣ d ∣) ⟩
      ∣ n ∣
      ∎

sign-mult-◃⁺
  : (n d : ℤ) .{{_ : NonZero n}} .{{_ : NonZero d}}
  → (sign (n * d) S.* sign d) ◃ ∣ n ∣ ≡ n
sign-mult-◃⁺ n d = begin
  (sign (n * d) S.* sign d) ◃ ∣ n ∣
  ≡⟨ cong (λ s → (s S.* sign d) ◃ ∣ n ∣) (sign-* n d {{i*j≢0 n d}}) ⟩
  ((sign n S.* sign d) S.* sign d) ◃ ∣ n ∣
  ≡⟨ cong (_◃ ∣ n ∣) (signs≡ n d) ⟩
  sign n ◃ ∣ n ∣
  ≡⟨ ◃-inverse n ⟩
  n
  ∎

sign-mult-◃ : (n d : ℤ) .{{_ : NonZero d}} → (sign (n * d) S.* sign d) ◃ ∣ n ∣ ≡ n
sign-mult-◃ +0 d = refl
sign-mult-◃ +[1+ m ] d = sign-mult-◃⁺ +[1+ m ] d
sign-mult-◃ -[1+ m ] d = sign-mult-◃⁺ -[1+ m ] d

quot-mult-law : (n d : ℤ) .{{_ : NonZero d}} → quot (n * d) d ≡ n
quot-mult-law n d = begin
  quot (n * d) d
  ≡⟨⟩
  (sign (n * d) S.* sign d) ◃ (∣ n * d ∣ ℕ./ ∣ d ∣)
  ≡⟨ cong (λ z → (sign (n * d) S.* sign d) ◃ (z ℕ./ ∣ d ∣)) (∣i*j∣≡∣i∣*∣j∣ n d) ⟩
  (sign (n * d) S.* sign d) ◃ (∣ n ∣ ℕ.* ∣ d ∣ ℕ./ ∣ d ∣)
  ≡⟨ cong (λ z → (sign (n * d) S.* sign d) ◃ z) (m*n/n≡m ∣ n ∣ ∣ d ∣) ⟩
  (sign (n * d) S.* sign d) ◃ ∣ n ∣
  ≡⟨ sign-mult-◃ n d ⟩
  n
  ∎

rem-mult-law : (n d : ℤ) .{{_ : NonZero d}} → rem (n * d) d ≡ 0ℤ
rem-mult-law n d = begin
  rem (n * d) d
  ≡⟨⟩
  sign (n * d) ◃ (∣ n * d ∣ ℕ.% ∣ d ∣)
  ≡⟨ cong (λ z → sign (n * d) ◃ (z ℕ.% ∣ d ∣)) (∣i*j∣≡∣i∣*∣j∣ n d) ⟩
  sign (n * d) ◃ (∣ n ∣ ℕ.* ∣ d ∣ ℕ.% ∣ d ∣)
  ≡⟨ cong (λ z → sign (n * d) ◃ z) (m*n%n≡0 ∣ n ∣ ∣ d ∣) ⟩
  0ℤ
  ∎

-- For fixed b, `remainderInteger _ b` is an additive homomorphism on non-negative integers
-- (a+a') `rem` b = ((a `rem` b) + (a' `rem` b)) `rem` b
rem-additive-pos-law
  : (a a' b : ℤ) .{{_ : NonNegative a}} .{{_ : NonNegative a'}} .{{_ : NonZero b}}
  → rem (a + a') b ≡ rem ((rem a b) + (rem a' b)) b 
rem-additive-pos-law (+_ m) (+_ n) b = begin
  rem (+ m + + n) b
  ≡⟨⟩
  sign (+ m + + n) ◃ (∣ + m + + n ∣ ℕ.% ∣ b ∣)
  ≡⟨⟩
  S.+ ◃ (∣ + m + + n ∣ ℕ.% ∣ b ∣)
  ≡⟨ +◃n≡+n _ ⟩
  + ((m ℕ.+ n) ℕ.% ∣ b ∣)
  ≡⟨ cong (+_) (%-distribˡ-+ m n ∣ b ∣) ⟩
  + ((m ℕ.% ∣ b ∣ ℕ.+ n ℕ.% ∣ b ∣) ℕ.% ∣ b ∣)
  ≡⟨ sym (+◃n≡+n _) ⟩
  S.+ ◃ (m ℕ.% ∣ b ∣ ℕ.+ n ℕ.% ∣ b ∣) ℕ.% ∣ b ∣
  ≡⟨ cong₂ (λ x y → rem (x + y) b) (sym (+◃n≡+n (m ℕ.% ∣ b ∣))) (sym (+◃n≡+n (n ℕ.% ∣ b ∣))) ⟩
  rem (rem (+ m) b + rem (+ n) b) b
  ∎

-- The remainder of zero is zero
rem-zero-law : (b : ℤ) .{{_ : NonZero b}} → rem 0ℤ b ≡ 0ℤ
rem-zero-law b = cong (S.+ ◃_) (m*n%n≡0 0 ∣ b ∣)

-- Negating an integer flips the sign it is built from
neg-◃ : (n : ℕ.ℕ) → - (S.+ ◃ n) ≡ S.- ◃ n
neg-◃ n = trans (cong (-_) (+◃n≡+n n)) (sym (-◃n≡-n n))

-- For fixed b, `remainderInteger _ b` is an odd function
rem-neg-law : (n b : ℤ) .{{_ : NonZero b}} → rem (- n) b ≡ - rem n b
rem-neg-law +0 b = trans (rem-zero-law b) (cong (-_) (sym (rem-zero-law b)))
rem-neg-law +[1+ m ] b = sym (neg-◃ (ℕ.suc m ℕ.% ∣ b ∣))
rem-neg-law -[1+ m ] b =
  trans (sym (neg-involutive (S.+ ◃ (ℕ.suc m ℕ.% ∣ b ∣))))
        (cong (-_) (neg-◃ (ℕ.suc m ℕ.% ∣ b ∣)))

-- The additive homomorphism law for non-positive integers, stated on the
-- negations of non-negative ones: it follows from `rem-additive-pos-law`
-- because `rem _ b` is odd and `-_` distributes over `_+_`
rem-additive-neg-law′
  : (a a' b : ℤ) .{{_ : NonNegative a}} .{{_ : NonNegative a'}} .{{_ : NonZero b}}
  → rem (- a + - a') b ≡ rem ((rem (- a) b) + (rem (- a') b)) b
rem-additive-neg-law′ a a' b = begin
  rem (- a + - a') b
  ≡⟨ cong (λ z → rem z b) (sym (neg-distrib-+ a a')) ⟩
  rem (- (a + a')) b
  ≡⟨ rem-neg-law (a + a') b ⟩
  - rem (a + a') b
  ≡⟨ cong (-_) (rem-additive-pos-law a a' b) ⟩
  - rem (rem a b + rem a' b) b
  ≡⟨ sym (rem-neg-law (rem a b + rem a' b) b) ⟩
  rem (- (rem a b + rem a' b)) b
  ≡⟨ cong (λ z → rem z b) (neg-distrib-+ (rem a b) (rem a' b)) ⟩
  rem (- rem a b + - rem a' b) b
  ≡⟨ cong₂ (λ x y → rem (x + y) b) (sym (rem-neg-law a b)) (sym (rem-neg-law a' b)) ⟩
  rem (rem (- a) b + rem (- a') b) b
  ∎

-- For fixed b, `remainderInteger _ b` is an additive homomorphism on non-positive integers
-- (a+a') `rem` b = ((a `rem` b) + (a' `rem` b)) `rem` b
rem-additive-neg-law
  : (a a' b : ℤ) .{{_ : NonPositive a}} .{{_ : NonPositive a'}} .{{_ : NonZero b}}
  → rem (a + a') b ≡ rem ((rem a b) + (rem a' b)) b
rem-additive-neg-law +0        +0        b = rem-additive-neg-law′ +0 +0 b
rem-additive-neg-law +0        -[1+ n ]  b = rem-additive-neg-law′ +0 +[1+ n ] b
rem-additive-neg-law -[1+ m ]  +0        b = rem-additive-neg-law′ +[1+ m ] +0 b
rem-additive-neg-law -[1+ m ]  -[1+ n ]  b = rem-additive-neg-law′ +[1+ m ] +[1+ n ] b

-- The two additive laws, packaged with the standard library's homomorphism
-- vocabulary. The domain must be ℕ rather than sign-restricted ℤ: the stdlib
-- morphism types quantify over the whole carrier, and the unrestricted law is
-- false for mixed signs (a = 4, a' = -2, b = 3 is a counterexample). The sign
-- is baked into the map instead: `rem (+ m) b` and `rem (- + m) b`.

-- The common target: ℤ with "add, then take the remainder by b"
rem-+-rawMonoid : (b : ℤ) .{{_ : NonZero b}} → RawMonoid 0ℓ 0ℓ
rem-+-rawMonoid b = record
  { Carrier = ℤ
  ; _≈_ = _≡_
  ; _∙_ = λ x y → rem (x + y) b
  ; ε = 0ℤ
  }

rem-+-isMonoidHomomorphism-pos
  : (b : ℤ) .{{_ : NonZero b}}
  → IsMonoidHomomorphism ℕ.+-0-rawMonoid (rem-+-rawMonoid b) (λ m → rem (+ m) b)
rem-+-isMonoidHomomorphism-pos b = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = cong (λ m → rem (+ m) b) }
    ; homo = λ m n → rem-additive-pos-law (+ m) (+ n) b
    }
  ; ε-homo = rem-zero-law b
  }

rem-+-isMonoidHomomorphism-neg
  : (b : ℤ) .{{_ : NonZero b}}
  → IsMonoidHomomorphism ℕ.+-0-rawMonoid (rem-+-rawMonoid b) (λ m → rem (- + m) b)
rem-+-isMonoidHomomorphism-neg b = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = cong (λ m → rem (- + m) b) }
    ; homo = λ m n → trans (cong (λ z → rem z b) (neg-distrib-+ (+ m) (+ n)))
                           (rem-additive-neg-law′ (+ m) (+ n) b)
    }
  ; ε-homo = rem-zero-law b
  }

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