---
title: Builtin.Integer.Properties
layout: page
---

This module proves the laws of the integer division operators defined in
`Builtin.Integer.Base`:

* `quot` and `rem` implement truncated division, following Haskell's
  `integerQuotRem#`;
* `div` and `mod` implement floored division, following Haskell's
  `integerDivMod#`.

The headline results are:

* `quotRem-law` and `divMod-law`, the round-trip identities
  `quot n d * d + rem n d ≡ n` and `div n d * d + mod n d ≡ n`,
  which are the defining specifications of the two division styles;
* `quot-mult-law` and `rem-mult-law`, dividing an exact multiple
  recovers the factor and leaves no remainder;
* `rem-zero-law` and `rem-neg-law`, for a fixed divisor, `rem` preserves
  zero and negation;
* `rem-additive-pos-law` and `rem-additive-neg-law`, for a fixed divisor,
  `rem` commutes with addition of same-signed arguments, packaged as monoid
  homomorphisms in `rem-+-isMonoidHomomorphism-pos` and
  `rem-+-isMonoidHomomorphism-neg`;
* `rem-mult-hom-law`, for a fixed divisor, `rem` commutes with
  multiplication — with no sign restriction;
* `rem-size-law` and the sign laws (`quot-nonNeg-law`, `rem-nonNeg-law`, …),
  the remainder is strictly smaller in magnitude than the divisor, the
  quotient's sign is the product of the operands' signs, and the remainder's
  sign follows the dividend;
* `div-mult-law` and `mod-mult-law`, the floored counterparts of the
  exact-multiple laws;
* `mod-size-pos-law` and `mod-size-neg-law`, `mod` lands in `[0, b)` for a
  positive divisor and in `(b, 0]` for a negative one, with the sign
  corollaries `mod-nonNeg-law`/`mod-nonPos-law` and the `div` sign laws;
* `divMod-unique-pos-law` and `divMod-unique-neg-law`, floored division is
  the unique solution of its specification — yielding
  `mod-plus-multiple-law` (periodicity) and finally `mod-additive-law` and
  `mod-multiplicative-law`, the unrestricted homomorphism laws for `mod`;
* `quotMaybe-correct` and friends, the `Maybe`-valued denotations exported
  to Haskell provably apply the genuine operators on every non-zero divisor
  and fail exactly on zero.

Together these prove every property in the Haskell test suites
`Evaluation.Builtins.Integer.QuotRemProperties` and
`Evaluation.Builtins.Integer.DivModProperties`. The division-by-zero failure
tests correspond to the `*Maybe-zero` lemmas about the partial denotations:
the total `quot`/`rem`/`div`/`mod` take a `NonZero` divisor instance, so for
them those cases are ruled out by typing.

Helper lemmas are kept in `private` blocks: they are proof machinery, not part
of the module's interface, and can be skipped on a first reading.

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
open import Data.Integer.Solver using (module +-*-Solver)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (yes; no)
open import Data.Maybe.Base using (just; nothing; map)
open import Data.Unit.Base using (tt)
```

## Helper lemmas about sign and ◃

The definitions of `quot` and `rem` decompose their arguments into a sign and
a magnitude, divide the magnitudes as naturals, and reassemble the results
with the standard library's `_◃_` operator. Accordingly, the proofs below all
hinge on a few facts about how `sign`, `_◃_` and `∣_∣` interact. The standard
library provides most of them (`◃-inverse`, `sign-*`, `+◃n≡+n`, `-◃n≡-n`, ...);
this section derives the remaining ones.

Multiplying by the same sign twice is the identity, since a sign is its own
inverse. This is a fact about `Data.Sign` alone; the proofs below use it with
`s = sign n` and `t = sign d` to cancel the divisor's sign.

```
private

  s*t*t≡s : (s t : S.Sign) → (s S.* t) S.* t ≡ s
  s*t*t≡s s t = begin
    (s S.* t) S.* t
    ≡⟨ SP.*-assoc s t t ⟩
    s S.* (t S.* t)
    ≡⟨ cong (s S.*_) (SP.s*s≡+ t) ⟩
    s S.* S.+
    ≡⟨ SP.*-identityʳ s ⟩
    s
    ∎
```

Reattaching the sign `sign (n * d) S.* sign d` to the magnitude of `n` gives
back `n`: the sign of the product decomposes as `sign n S.* sign d`, and the
divisor's sign then cancels by `s*t*t≡s`. This is exactly the sign expression
appearing in `quot`, so this lemma is the crux of `quot-mult-law`. The
decomposition of `sign (n * d)` requires `n * d` to be non-zero, hence a first
version restricted to non-zero `n`; the general version treats `n ≡ 0ℤ` by
computation.

```
private

  sign-mult-◃⁺
    : (n d : ℤ) .{{_ : NonZero n}} .{{_ : NonZero d}}
    → (sign (n * d) S.* sign d) ◃ ∣ n ∣ ≡ n
  sign-mult-◃⁺ n d = begin
    (sign (n * d) S.* sign d) ◃ ∣ n ∣
    ≡⟨ cong (λ s → (s S.* sign d) ◃ ∣ n ∣) (sign-* n d {{i*j≢0 n d}}) ⟩
    ((sign n S.* sign d) S.* sign d) ◃ ∣ n ∣
    ≡⟨ cong (_◃ ∣ n ∣) (s*t*t≡s (sign n) (sign d)) ⟩
    sign n ◃ ∣ n ∣
    ≡⟨ ◃-inverse n ⟩
    n
    ∎

  sign-mult-◃ : (n d : ℤ) .{{_ : NonZero d}} → (sign (n * d) S.* sign d) ◃ ∣ n ∣ ≡ n
  sign-mult-◃ +0 d = refl
  sign-mult-◃ +[1+ m ] d = sign-mult-◃⁺ +[1+ m ] d
  sign-mult-◃ -[1+ m ] d = sign-mult-◃⁺ -[1+ m ] d
```

Negating an integer flips the sign it is built from.

```
private

  neg-◃ : (n : ℕ.ℕ) → - (S.+ ◃ n) ≡ S.- ◃ n
  neg-◃ n = trans (cong (-_) (+◃n≡+n n)) (sym (-◃n≡-n n))
```

Attaching a positive sign to any magnitude yields a non-negative integer,
and a negative sign a non-positive one. Both are proved by case on the
magnitude, since `_◃_` computes on it.

```
private

  0≤+◃ : (n : ℕ.ℕ) → 0ℤ ≤ (S.+ ◃ n)
  0≤+◃ ℕ.zero    = +≤+ ℕ.z≤n
  0≤+◃ (ℕ.suc n) = +≤+ ℕ.z≤n

  -◃≤0 : (n : ℕ.ℕ) → (S.- ◃ n) ≤ 0ℤ
  -◃≤0 ℕ.zero    = +≤+ ℕ.z≤n
  -◃≤0 (ℕ.suc n) = -≤+
```

## Properties of quot and rem

Truncated division is correct: quotient times divisor plus remainder gives
back the dividend. This is the defining specification of Haskell's `quotRem`.
The proof pushes the statement down to the corresponding law for natural
number division (`m≡m%n+[m/n]*n`) by decomposing all integers into signs and
magnitudes.

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
  ≡⟨ cong (λ s → (s ◃ (q ℕ.* ∣ d ∣)) + (sign n ◃ r)) (s*t*t≡s (sign n) (sign d)) ⟩
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
```

Dividing an exact multiple recovers the factor, and the corresponding
remainder is zero. Both statements reduce to their natural-number analogues
(`m*n/n≡m` and `m*n%n≡0`) on the magnitudes; recovering the factor's sign is
the job of the `sign-mult-◃` helper.

```
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
```

For a fixed divisor `b`, the function `rem _ b` preserves zero and negation
(it is an odd function).

```
rem-zero-law : (b : ℤ) .{{_ : NonZero b}} → rem 0ℤ b ≡ 0ℤ
rem-zero-law b = cong (S.+ ◃_) (m*n%n≡0 0 ∣ b ∣)

rem-neg-law : (n b : ℤ) .{{_ : NonZero b}} → rem (- n) b ≡ - rem n b
rem-neg-law +0 b       = trans (rem-zero-law b) (cong (-_) (sym (rem-zero-law b)))
rem-neg-law +[1+ m ] b = sym (neg-◃ (ℕ.suc m ℕ.% ∣ b ∣))
rem-neg-law -[1+ m ] b = 
  trans (sym (neg-involutive (S.+ ◃ (ℕ.suc m ℕ.% ∣ b ∣))))
        (cong (-_) (neg-◃ (ℕ.suc m ℕ.% ∣ b ∣)))
```

## Sign and size of quot and rem

The remainder is strictly smaller in magnitude than the divisor. This is
immediate from the corresponding bound for natural number division
(`m%n<n`), since building an integer with `_◃_` preserves the magnitude
(`abs-◃`).

```
rem-size-law : (a b : ℤ) .{{_ : NonZero b}} → ∣ rem a b ∣ ℕ.< ∣ b ∣
rem-size-law a b =
  subst (ℕ._< ∣ b ∣)
        (sym (abs-◃ (sign a) (∣ a ∣ ℕ.% ∣ b ∣)))
        (m%n<n ∣ a ∣ ∣ b ∣)
```

The quotient's sign is the product of the operands' signs, so it is
determined by the four sign combinations of the operands. Case analysis on
the integer constructors makes the sign product compute; the `a = +0`
corner in the mixed-sign cases is harmless because the quotient magnitude
`0 / ∣ b ∣` computes to `0`, and `s ◃ 0` is `+0` for either sign.

```
quot-nonNeg-law
  : (a b : ℤ) .{{_ : NonNegative a}} .{{_ : NonZero b}} .{{_ : Positive b}}
  → 0ℤ ≤ quot a b
quot-nonNeg-law (+ m) +[1+ n ] = 0≤+◃ (m ℕ./ ℕ.suc n)

quot-nonPos-pos-law
  : (a b : ℤ) .{{_ : NonPositive a}} .{{_ : NonZero b}} .{{_ : Positive b}}
  → quot a b ≤ 0ℤ
quot-nonPos-pos-law +0       +[1+ n ] = +≤+ ℕ.z≤n
quot-nonPos-pos-law -[1+ m ] +[1+ n ] = -◃≤0 (ℕ.suc m ℕ./ ℕ.suc n)

quot-nonNeg-neg-law
  : (a b : ℤ) .{{_ : NonNegative a}} .{{_ : NonZero b}} .{{_ : Negative b}} →
  quot a b ≤ 0ℤ
quot-nonNeg-neg-law (+ m) -[1+ n ] = -◃≤0 (m ℕ./ ℕ.suc n)

quot-nonPos-neg-law
  : (a b : ℤ) .{{_ : NonPositive a}} .{{_ : NonZero b}} .{{_ : Negative b}} →
  0ℤ ≤ quot a b
quot-nonPos-neg-law +0       -[1+ n ] = +≤+ ℕ.z≤n
quot-nonPos-neg-law -[1+ m ] -[1+ n ] = 0≤+◃ (ℕ.suc m ℕ./ ℕ.suc n)
```

The remainder carries the dividend's sign, whatever the divisor's sign is.
(In the Haskell test suite this is four properties, one per sign
combination of the operands; the divisor's sign is irrelevant here.)

```
rem-nonNeg-law
  : (a b : ℤ) .{{_ : NonNegative a}} .{{_ : NonZero b}} → 0ℤ ≤ rem a b
rem-nonNeg-law (+ m) b = 0≤+◃ (m ℕ.% ∣ b ∣)

rem-nonPos-law
  : (a b : ℤ) .{{_ : NonPositive a}} .{{_ : NonZero b}} → rem a b ≤ 0ℤ
rem-nonPos-law +0       b = ≤-reflexive (rem-zero-law b)
rem-nonPos-law -[1+ m ] b = -◃≤0 (ℕ.suc m ℕ.% ∣ b ∣)
```

For a fixed divisor `b`, `rem _ b` commutes with addition, provided both
arguments have the same sign:

    rem (a + a') b ≡ rem (rem a b + rem a' b) b

The same-sign restriction is essential: for mixed signs the law fails, e.g.
with `a = 4`, `a' = -2`, `b = 3` the left-hand side is `rem 2 3 = 2` while the
right-hand side is `rem (1 + -2) 3 = -1`.

```
_ : rem ((+ 4) + (- (+ 2))) (+ 3) ≢ rem (rem (+ 4) (+ 3) + rem (- (+ 2)) (+ 3)) (+ 3)
_ = λ ()
```

The non-negative case follows from the corresponding law for natural number
division (`%-distribˡ-+`).

```
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
```

The non-positive case reduces to the non-negative one: `rem _ b` is odd and
`-_` distributes over `_+_`. The private lemma states the law on the
negations of non-negative integers, which is what the reduction produces;
the public law then converts between the two phrasings of "non-positive" by
pattern matching.

```
private

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

rem-additive-neg-law
  : (a a' b : ℤ) .{{_ : NonPositive a}} .{{_ : NonPositive a'}} .{{_ : NonZero b}}
  → rem (a + a') b ≡ rem ((rem a b) + (rem a' b)) b
rem-additive-neg-law +0        +0        b = rem-additive-neg-law′ +0 +0 b
rem-additive-neg-law +0        -[1+ n ]  b = rem-additive-neg-law′ +0 +[1+ n ] b
rem-additive-neg-law -[1+ m ]  +0        b = rem-additive-neg-law′ +[1+ m ] +0 b
rem-additive-neg-law -[1+ m ]  -[1+ n ]  b = rem-additive-neg-law′ +[1+ m ] +[1+ n ] b
```

## rem and multiplication

For a fixed divisor `b`, `rem _ b` also commutes with multiplication:

    rem (a * a') b ≡ rem (rem a b * rem a' b) b

Unlike the additive law, this needs no same-sign restriction, because
multiplication commutes with negation on either argument
(`- (i * j) ≡ (- i) * j ≡ i * (- j)`), so every sign combination reduces to
the non-negative case via the oddness of `rem _ b` (`rem-neg-law`). The
non-negative case is the natural-number law `%-distribˡ-*` on the magnitudes.

```
private

  rem-mult-pos-law
    : (a a' b : ℤ) .{{_ : NonNegative a}} .{{_ : NonNegative a'}} .{{_ : NonZero b}}
    → rem (a * a') b ≡ rem ((rem a b) * (rem a' b)) b
  rem-mult-pos-law (+ m) (+ n) b = begin
    rem (+ m * + n) b
    ≡⟨ cong (λ z → rem z b) (sym (pos-* m n)) ⟩
    rem (+ (m ℕ.* n)) b
    ≡⟨⟩
    S.+ ◃ ((m ℕ.* n) ℕ.% ∣ b ∣)
    ≡⟨ cong (S.+ ◃_) (%-distribˡ-* m n ∣ b ∣) ⟩
    S.+ ◃ (((m ℕ.% ∣ b ∣) ℕ.* (n ℕ.% ∣ b ∣)) ℕ.% ∣ b ∣)
    ≡⟨⟩
    rem (+ ((m ℕ.% ∣ b ∣) ℕ.* (n ℕ.% ∣ b ∣))) b
    ≡⟨ cong (λ z → rem z b) (pos-* (m ℕ.% ∣ b ∣) (n ℕ.% ∣ b ∣)) ⟩
    rem (+ (m ℕ.% ∣ b ∣) * + (n ℕ.% ∣ b ∣)) b
    ≡⟨ cong₂ (λ x y → rem (x * y) b)
             (sym (+◃n≡+n (m ℕ.% ∣ b ∣))) (sym (+◃n≡+n (n ℕ.% ∣ b ∣))) ⟩
    rem (rem (+ m) b * rem (+ n) b) b
    ∎
```

The transfer to the other sign combinations, using that `rem _ b` is odd
and negation distributes over multiplication:

```
private

  rem-mult-negˡ-law
    : (a a' b : ℤ) .{{_ : NonNegative a}} .{{_ : NonNegative a'}} .{{_ : NonZero b}}
    → rem ((- a) * a') b ≡ rem ((rem (- a) b) * (rem a' b)) b
  rem-mult-negˡ-law a a' b = begin
    rem (- a * a') b
    ≡⟨ cong (λ z → rem z b) (sym (neg-distribˡ-* a a')) ⟩
    rem (- (a * a')) b
    ≡⟨ rem-neg-law (a * a') b ⟩
    - rem (a * a') b
    ≡⟨ cong (-_) (rem-mult-pos-law a a' b) ⟩
    - rem (rem a b * rem a' b) b
    ≡⟨ sym (rem-neg-law (rem a b * rem a' b) b) ⟩
    rem (- (rem a b * rem a' b)) b
    ≡⟨ cong (λ z → rem z b) (neg-distribˡ-* (rem a b) (rem a' b)) ⟩
    rem ((- rem a b) * rem a' b) b
    ≡⟨ cong (λ z → rem (z * rem a' b) b) (sym (rem-neg-law a b)) ⟩
    rem (rem (- a) b * rem a' b) b
    ∎

  rem-mult-negʳ-law
    : (a a' b : ℤ) .{{_ : NonNegative a}} .{{_ : NonNegative a'}} .{{_ : NonZero b}}
    → rem (a * (- a')) b ≡ rem ((rem a b) * (rem (- a') b)) b
  rem-mult-negʳ-law a a' b = begin
    rem (a * - a') b
    ≡⟨ cong (λ z → rem z b) (sym (neg-distribʳ-* a a')) ⟩
    rem (- (a * a')) b
    ≡⟨ rem-neg-law (a * a') b ⟩
    - rem (a * a') b
    ≡⟨ cong (-_) (rem-mult-pos-law a a' b) ⟩
    - rem (rem a b * rem a' b) b
    ≡⟨ sym (rem-neg-law (rem a b * rem a' b) b) ⟩
    rem (- (rem a b * rem a' b)) b
    ≡⟨ cong (λ z → rem z b) (neg-distribʳ-* (rem a b) (rem a' b)) ⟩
    rem (rem a b * (- rem a' b)) b
    ≡⟨ cong (λ z → rem (rem a b * z) b) (sym (rem-neg-law a' b)) ⟩
    rem (rem a b * rem (- a') b) b
    ∎

  rem-mult-neg²-law
    : (a a' b : ℤ) .{{_ : NonNegative a}} .{{_ : NonNegative a'}} .{{_ : NonZero b}}
    → rem ((- a) * (- a')) b ≡ rem ((rem (- a) b) * (rem (- a') b)) b
  rem-mult-neg²-law a a' b = begin
    rem (- a * - a') b
    ≡⟨ cong (λ z → rem z b) (sym (neg-distribˡ-* a (- a'))) ⟩
    rem (- (a * - a')) b
    ≡⟨ rem-neg-law (a * - a') b ⟩
    - rem (a * - a') b
    ≡⟨ cong (-_) (rem-mult-negʳ-law a a' b) ⟩
    - rem (rem a b * rem (- a') b) b
    ≡⟨ sym (rem-neg-law (rem a b * rem (- a') b) b) ⟩
    rem (- (rem a b * rem (- a') b)) b
    ≡⟨ cong (λ z → rem z b) (neg-distribˡ-* (rem a b) (rem (- a') b)) ⟩
    rem ((- rem a b) * rem (- a') b) b
    ≡⟨ cong (λ z → rem (z * rem (- a') b) b) (sym (rem-neg-law a b)) ⟩
    rem (rem (- a) b * rem (- a') b) b
    ∎
```

The public law dispatches on the constructors; the negative cases
typecheck against the helpers because `- +[1+ k ]` reduces to `-[1+ k ]`
definitionally.

```
rem-mult-hom-law
  : (a a' b : ℤ) .{{_ : NonZero b}}
  → rem (a * a') b ≡ rem ((rem a b) * (rem a' b)) b
rem-mult-hom-law (+ m)    (+ n)    b = rem-mult-pos-law  (+ m)    (+ n)    b
rem-mult-hom-law (+ m)    -[1+ n ] b = rem-mult-negʳ-law (+ m)    +[1+ n ] b
rem-mult-hom-law -[1+ m ] (+ n)    b = rem-mult-negˡ-law +[1+ m ] (+ n)    b
rem-mult-hom-law -[1+ m ] -[1+ n ] b = rem-mult-neg²-law +[1+ m ] +[1+ n ] b
```

## Properties of div and mod

Floored division is defined in `Builtin.Integer.Base` by adjusting the result
of truncated division: when the remainder is non-zero and its sign disagrees
with the divisor's, `divModFixup` decrements the quotient and adds the divisor
to the remainder. The fixup preserves the quotient-remainder identity, because

    (q - 1) * d + (r + d) ≡ q * d + r

which is the rearrangement proved by the private `predFixup` lemma.

```
private

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

divModFixup-law : (q r d : ℤ) → proj₁ (divModFixup q r d) * d + proj₂ (divModFixup q r d) ≡ q * d + r
divModFixup-law q +0         d          = refl
divModFixup-law q +[1+ _ ]   (+ _)      = refl
divModFixup-law q +[1+ _ ]   (-[1+ _ ]) = predFixup q _ _
divModFixup-law q (-[1+ _ ]) (+ _)      = predFixup q _ _
divModFixup-law q (-[1+ _ ]) (-[1+ _ ]) = refl
```

Floored division is correct: quotient times divisor plus remainder gives back
the dividend. It follows from the truncated law `quotRem-law`, since the fixup
preserves the identity.

```
divMod-law : (n d : ℤ) .{{_ : NonZero d}} → (div n d) * d + (mod n d) ≡ n
divMod-law n d = begin
  div n d * d + mod n d
  ≡⟨ divModFixup-law (quot n d) (rem n d) d ⟩
  quot n d * d + rem n d
  ≡⟨ quotRem-law n d ⟩
  n
  ∎
```

## div and mod under negation

Negating both operands leaves the quotient unchanged and negates the
remainder — for truncated division this is immediate from the definitions
(both `sign` factors flip, magnitudes are untouched), and the fixup respects
it, so it carries over to floored division. These symmetries let every
negative-divisor result below be derived from its positive-divisor
counterpart.

```
private

  divModFixup-neg
    : (q r d : ℤ) .{{_ : NonZero d}}
    → divModFixup q (- r) (- d)
    ≡ (proj₁ (divModFixup q r d) , - proj₂ (divModFixup q r d))
  divModFixup-neg q +0         +[1+ n ] = refl
  divModFixup-neg q +0         -[1+ n ] = refl
  divModFixup-neg q +[1+ m ]   +[1+ n ] = refl
  divModFixup-neg q +[1+ m ]   -[1+ n ] = cong (pred q ,_) (⊖-swap (ℕ.suc n) (ℕ.suc m))
  divModFixup-neg q (-[1+ m ]) +[1+ n ] = cong (pred q ,_) (⊖-swap (ℕ.suc m) (ℕ.suc n))
  divModFixup-neg q (-[1+ m ]) -[1+ n ] = refl

quot-neg-neg-law
  : (n d : ℤ) .{{_ : NonZero d}} .{{_ : NonZero (- d)}}
  → quot (- n) (- d) ≡ quot n d
quot-neg-neg-law +0       +[1+ k ] = refl
quot-neg-neg-law +0       -[1+ k ] = refl
quot-neg-neg-law +[1+ m ] +[1+ k ] = refl
quot-neg-neg-law +[1+ m ] -[1+ k ] = refl
quot-neg-neg-law -[1+ m ] +[1+ k ] = refl
quot-neg-neg-law -[1+ m ] -[1+ k ] = refl

rem-neg-neg-law
  : (n d : ℤ) .{{_ : NonZero d}} .{{_ : NonZero (- d)}}
  → rem (- n) (- d) ≡ - rem n d
rem-neg-neg-law n +[1+ k ] = rem-neg-law n -[1+ k ]
rem-neg-neg-law n -[1+ k ] = rem-neg-law n +[1+ k ]

div-neg-neg-law
  : (n d : ℤ) .{{_ : NonZero d}} .{{_ : NonZero (- d)}}
  → div (- n) (- d) ≡ div n d
div-neg-neg-law n d = trans
  (cong₂ (λ x y → proj₁ (divModFixup x y (- d))) (quot-neg-neg-law n d) (rem-neg-neg-law n d))
  (cong proj₁ (divModFixup-neg (quot n d) (rem n d) d))

mod-neg-neg-law
  : (n d : ℤ) .{{_ : NonZero d}} .{{_ : NonZero (- d)}}
  → mod (- n) (- d) ≡ - mod n d
mod-neg-neg-law n d = trans
  (cong₂ (λ x y → proj₂ (divModFixup x y (- d))) (quot-neg-neg-law n d) (rem-neg-neg-law n d))
  (cong proj₂ (divModFixup-neg (quot n d) (rem n d) d))
```

## Dividing exact multiples

Floored division of an exact multiple recovers the factor and leaves no
remainder. The remainder of the underlying truncated division is zero
(`rem-mult-law`), and the fixup does nothing when the remainder is zero,
so the result is that of `quot-mult-law`.

```
div-mult-law : (k b : ℤ) .{{_ : NonZero b}} → div (k * b) b ≡ k
div-mult-law k b = begin
  proj₁ (divModFixup (quot (k * b) b) (rem (k * b) b) b)
  ≡⟨ cong (λ r → proj₁ (divModFixup (quot (k * b) b) r b)) (rem-mult-law k b) ⟩
  quot (k * b) b
  ≡⟨ quot-mult-law k b ⟩
  k
  ∎

mod-mult-law : (k b : ℤ) .{{_ : NonZero b}} → mod (k * b) b ≡ 0ℤ
mod-mult-law k b =
  cong (λ r → proj₂ (divModFixup (quot (k * b) b) r b)) (rem-mult-law k b)
```

## The range of mod

The result of `mod` lies between zero and the divisor: in `[0, b)` for a
positive divisor, in `(b, 0]` for a negative one — this is the defining
range of floored division, in contrast to `rem`, whose sign follows the
dividend. The proof analyzes the remainder cases of the fixup: when no
fixup happens the bounds come from the sign and size of `rem`; when it does,
the adjusted remainder `rem + b` lands in range precisely because
`∣ rem ∣ < ∣ b ∣`.

```
mod-size-pos-law
  : (a b : ℤ) .{{_ : NonZero b}} .{{_ : Positive b}}
  → (0ℤ ≤ mod a b) × (mod a b < b)
mod-size-pos-law a b@(+[1+ n ]) with rem a b in eq
... | +0       = +≤+ ℕ.z≤n , +<+ ℕ.z<s
... | +[1+ m ] = +≤+ ℕ.z≤n , +<+ sm<sn
  where
    sm<sn : ℕ.suc m ℕ.< ℕ.suc n
    sm<sn = subst (ℕ._< ℕ.suc n) (cong ∣_∣ eq) (rem-size-law a b)
... | -[1+ m ] = 0≤fix , m⊖1+n<m (ℕ.suc n) (ℕ.suc m)
  where
    sm≤sn : ℕ.suc m ℕ.≤ ℕ.suc n
    sm≤sn = ℕP.<⇒≤ (subst (ℕ._< ℕ.suc n) (cong ∣_∣ eq) (rem-size-law a b))
    0≤fix : 0ℤ ≤ ℕ.suc n ⊖ ℕ.suc m
    0≤fix = subst (0ℤ ≤_) (sym (≤-⊖ sm≤sn)) (+≤+ ℕ.z≤n)

mod-size-neg-law
  : (a b : ℤ) .{{_ : NonZero b}} .{{_ : Negative b}}
  → (b < mod a b) × (mod a b ≤ 0ℤ)
mod-size-neg-law a b@(-[1+ n ]) =
  subst (b <_)   (sym eqm) (neg-mono-< (proj₂ sizes)) ,
  subst (_≤ 0ℤ) (sym eqm) (neg-mono-≤ (proj₁ sizes))
  where
    sizes = mod-size-pos-law (- a) +[1+ n ]
    eqm : mod a b ≡ - mod (- a) +[1+ n ]
    eqm = trans (sym (neg-involutive (mod a b)))
                (cong (-_) (sym (mod-neg-neg-law a b)))
```

The corresponding sign facts (four properties in the Haskell test suite —
the sign of `mod` follows the divisor, whatever the dividend's sign):

```
mod-nonNeg-law
  : (a b : ℤ) .{{_ : NonZero b}} .{{_ : Positive b}} → 0ℤ ≤ mod a b
mod-nonNeg-law a b = proj₁ (mod-size-pos-law a b)

mod-nonPos-law
  : (a b : ℤ) .{{_ : NonZero b}} .{{_ : Negative b}} → mod a b ≤ 0ℤ
mod-nonPos-law a b = proj₂ (mod-size-neg-law a b)
```

## Sign of div

Like `quot`, the sign of `div` is the product of the operands' signs. For a
positive divisor the fixup can only decrement the quotient, which is
harmless for the non-positive bound and never fires for the non-negative
one (the remainder has the dividend's sign, so no sign disagreement is
possible); the impossible branches are discharged against the sign of
`rem`. The negative-divisor cases follow by the negation symmetry.

```
private

  nonNeg⇒nonPos-neg : ∀ {i} → .{{NonNegative i}} → NonPositive (- i)
  nonNeg⇒nonPos-neg {+0}       = record { nonPos = tt }
  nonNeg⇒nonPos-neg {+[1+ n ]} = record { nonPos = tt }

  nonPos⇒nonNeg-neg : ∀ {i} → .{{NonPositive i}} → NonNegative (- i)
  nonPos⇒nonNeg-neg {+0}        = record { nonNeg = tt }
  nonPos⇒nonNeg-neg { -[1+ n ]} = record { nonNeg = tt }

div-nonNeg-law
  : (a b : ℤ) .{{_ : NonNegative a}} .{{_ : NonZero b}} .{{_ : Positive b}}
  → 0ℤ ≤ div a b
div-nonNeg-law a b@(+[1+ n ]) with rem a b in eq
... | +0       = quot-nonNeg-law a b
... | +[1+ m ] = quot-nonNeg-law a b
... | -[1+ m ] = contradiction (subst (0ℤ ≤_) eq (rem-nonNeg-law a b)) λ ()

div-nonPos-pos-law
  : (a b : ℤ) .{{_ : NonPositive a}} .{{_ : NonZero b}} .{{_ : Positive b}}
  → div a b ≤ 0ℤ
div-nonPos-pos-law a b@(+[1+ n ]) with rem a b in eq
... | +0       = quot-nonPos-pos-law a b
... | +[1+ m ] = contradiction (subst (_≤ 0ℤ) eq (rem-nonPos-law a b)) λ { (+≤+ ()) }
... | -[1+ m ] = i≤j⇒pred[i]≤j (quot-nonPos-pos-law a b)

div-nonNeg-neg-law
  : (a b : ℤ) .{{_ : NonNegative a}} .{{_ : NonZero b}} .{{_ : Negative b}}
  → div a b ≤ 0ℤ
div-nonNeg-neg-law a b@(-[1+ n ]) =
  subst (_≤ 0ℤ) (div-neg-neg-law a b)
        (div-nonPos-pos-law (- a) +[1+ n ] {{nonNeg⇒nonPos-neg}})

div-nonPos-neg-law
  : (a b : ℤ) .{{_ : NonPositive a}} .{{_ : NonZero b}} .{{_ : Negative b}}
  → 0ℤ ≤ div a b
div-nonPos-neg-law a b@(-[1+ n ]) =
  subst (0ℤ ≤_) (div-neg-neg-law a b)
        (div-nonNeg-law (- a) +[1+ n ] {{nonPos⇒nonNeg-neg}})
```

## Uniqueness of floored division

The pair `(div n b , mod n b)` is the unique solution of the specification
"`n ≡ q * b + r` with `r` in the floored range": any candidate pair
satisfying it must be the real one. The heart of the proof is a sandwich
argument on the quotients: two representations with in-range remainders
force `q₂ * b < suc q₁ * b`, hence `q₂ ≤ q₁`, in both directions.

```
private

  +-cancelˡ′ : (i : ℤ) {j k : ℤ} → i + j ≡ i + k → j ≡ k
  +-cancelˡ′ i {j} {k} eq = begin
    j             ≡⟨ sym (+-identityˡ j) ⟩
    0ℤ + j        ≡⟨ cong (_+ j) (sym (+-inverseˡ i)) ⟩
    (- i + i) + j ≡⟨ +-assoc (- i) i j ⟩
    - i + (i + j) ≡⟨ cong (λ z → - i + z) eq ⟩
    - i + (i + k) ≡⟨ sym (+-assoc (- i) i k) ⟩
    (- i + i) + k ≡⟨ cong (_+ k) (+-inverseˡ i) ⟩
    0ℤ + k        ≡⟨ +-identityˡ k ⟩
    k             ∎

  quotient-≤ : (q₁ r₁ q₂ r₂ : ℤ) (n : ℕ.ℕ)
    → 0ℤ ≤ r₂ → r₁ < +[1+ n ]
    → q₁ * +[1+ n ] + r₁ ≡ q₂ * +[1+ n ] + r₂
    → q₂ ≤ q₁
  quotient-≤ q₁ r₁ q₂ r₂ n 0≤r₂ r₁<b hyp =
    subst (q₂ ≤_) (pred-suc q₁) (i<j⇒i≤pred[j] q₂<sucq₁)
    where
      b = +[1+ n ]
      step₁ : q₂ * b ≤ q₁ * b + r₁
      step₁ = subst (q₂ * b ≤_) (sym hyp) (i≤i+j (q₂ * b) r₂ {{nonNegative 0≤r₂}})
      step₂ : q₁ * b + r₁ < suc q₁ * b
      step₂ = subst (q₁ * b + r₁ <_)
                    (trans (+-comm (q₁ * b) b) (sym (suc-* q₁ b)))
                    (+-monoʳ-< (q₁ * b) r₁<b)
      q₂<sucq₁ : q₂ < suc q₁
      q₂<sucq₁ = *-cancelʳ-<-nonNeg b (≤-<-trans step₁ step₂)

divMod-unique-pos-law
  : (n q r b : ℤ) .{{_ : NonZero b}} .{{_ : Positive b}}
  → 0ℤ ≤ r → r < b → n ≡ q * b + r
  → (q ≡ div n b) × (r ≡ mod n b)
divMod-unique-pos-law n q r b@(+[1+ k ]) 0≤r r<b n≡qb+r = q≡ , r≡
  where
    eq : q * b + r ≡ div n b * b + mod n b
    eq = trans (sym n≡qb+r) (sym (divMod-law n b))
    sizes = mod-size-pos-law n b
    q≡ : q ≡ div n b
    q≡ = ≤-antisym
           (quotient-≤ (div n b) (mod n b) q r k 0≤r (proj₂ sizes) (sym eq))
           (quotient-≤ q r (div n b) (mod n b) k (proj₁ sizes) r<b eq)
    r≡ : r ≡ mod n b
    r≡ = +-cancelˡ′ (q * b)
           (trans eq (cong (λ z → z * b + mod n b) (sym q≡)))

divMod-unique-neg-law
  : (n q r b : ℤ) .{{_ : NonZero b}} .{{_ : Negative b}}
  → b < r → r ≤ 0ℤ → n ≡ q * b + r
  → (q ≡ div n b) × (r ≡ mod n b)
divMod-unique-neg-law n q r b@(-[1+ k ]) b<r r≤0 n≡qb+r =
  trans (proj₁ uniq) (div-neg-neg-law n b) ,
  neg-injective (trans (proj₂ uniq) (mod-neg-neg-law n b))
  where
    -n≡ : - n ≡ q * +[1+ k ] + (- r)
    -n≡ = trans (cong (-_) n≡qb+r)
          (trans (neg-distrib-+ (q * b) r)
                 (cong (_+ (- r)) (neg-distribʳ-* q b)))
    uniq = divMod-unique-pos-law (- n) q (- r) +[1+ k ]
             (neg-mono-≤ r≤0) (neg-mono-< b<r) -n≡
```

## mod is invariant under adding multiples of the divisor

The keystone corollary of uniqueness: adding `k * b` to the dividend shifts
the quotient by `k` and leaves the remainder unchanged. Together with the
quotient-remainder identity, this is what makes `mod _ b` genuinely periodic
— and, unlike at the `rem` level, valid for arbitrary signs.

```
private

  rearrange : (x k b : ℤ) .{{_ : NonZero b}}
    → x + k * b ≡ (div x b + k) * b + mod x b
  rearrange x k b =
    trans (cong (_+ k * b) (sym (divMod-law x b)))
          (shuffle (div x b) (mod x b) k b)
    where
      shuffle : ∀ p u q w → (p * w + u) + q * w ≡ (p + q) * w + u
      shuffle = solve 4 (λ p u q w →
                  ((p :* w) :+ u) :+ (q :* w) := ((p :+ q) :* w) :+ u) refl
        where open +-*-Solver

div-plus-multiple-law
  : (x k b : ℤ) .{{_ : NonZero b}} → div (x + k * b) b ≡ div x b + k
div-plus-multiple-law x k b@(+[1+ n ]) =
  sym (proj₁ (divMod-unique-pos-law (x + k * b) (div x b + k) (mod x b) b
        (proj₁ (mod-size-pos-law x b)) (proj₂ (mod-size-pos-law x b))
        (rearrange x k b)))
div-plus-multiple-law x k b@(-[1+ n ]) =
  sym (proj₁ (divMod-unique-neg-law (x + k * b) (div x b + k) (mod x b) b
        (proj₁ (mod-size-neg-law x b)) (proj₂ (mod-size-neg-law x b))
        (rearrange x k b)))

mod-plus-multiple-law
  : (x k b : ℤ) .{{_ : NonZero b}} → mod (x + k * b) b ≡ mod x b
mod-plus-multiple-law x k b@(+[1+ n ]) =
  sym (proj₂ (divMod-unique-pos-law (x + k * b) (div x b + k) (mod x b) b
        (proj₁ (mod-size-pos-law x b)) (proj₂ (mod-size-pos-law x b))
        (rearrange x k b)))
mod-plus-multiple-law x k b@(-[1+ n ]) =
  sym (proj₂ (divMod-unique-neg-law (x + k * b) (div x b + k) (mod x b) b
        (proj₁ (mod-size-neg-law x b)) (proj₂ (mod-size-neg-law x b))
        (rearrange x k b)))
```

## mod is additive and multiplicative

For a fixed divisor `b`, `mod _ b` is both an additive and a multiplicative
homomorphism — with no sign restrictions, unlike the corresponding laws for
`rem`. Both proofs expand the operands with the quotient-remainder identity,
collect everything that is a multiple of `b`, and discard it with
`mod-plus-multiple-law`.

```
mod-additive-law
  : (a a' b : ℤ) .{{_ : NonZero b}}
  → mod (a + a') b ≡ mod ((mod a b) + (mod a' b)) b
mod-additive-law a a' b = begin
  mod (a + a') b
  ≡⟨ cong (λ z → mod z b) expand ⟩
  mod ((mod a b + mod a' b) + (div a b + div a' b) * b) b
  ≡⟨ mod-plus-multiple-law (mod a b + mod a' b) (div a b + div a' b) b ⟩
  mod (mod a b + mod a' b) b
  ∎
  where
    shuffle : ∀ p u q v w → (p * w + u) + (q * w + v) ≡ (u + v) + (p + q) * w
    shuffle =
      solve
        5
        (λ p u q v w →
          ((p :* w) :+ u) :+ ((q :* w) :+ v)
          := (u :+ v) :+ ((p :+ q) :* w)
        )
        refl
      where open +-*-Solver
    expand : a + a' ≡ (mod a b + mod a' b) + (div a b + div a' b) * b
    expand =
      trans
      (cong₂ _+_ (sym (divMod-law a b)) (sym (divMod-law a' b)))
      (shuffle (div a b) (mod a b) (div a' b) (mod a' b) b)

mod-multiplicative-law
  : (a a' b : ℤ) .{{_ : NonZero b}}
  → mod (a * a') b ≡ mod ((mod a b) * (mod a' b)) b
mod-multiplicative-law a a' b = begin
  mod (a * a') b
  ≡⟨ cong (λ z → mod z b) expand ⟩
  mod ((mod a b * mod a' b)
       + (div a b * div a' b * b + div a b * mod a' b + mod a b * div a' b) * b) b
  ≡⟨ mod-plus-multiple-law (mod a b * mod a' b)
       (div a b * div a' b * b + div a b * mod a' b + mod a b * div a' b) b ⟩
  mod (mod a b * mod a' b) b
  ∎
  where
    expand
      : a * a' ≡ (mod a b * mod a' b) + (div a b * div a' b * b + div a b * mod a' b + mod a b * div a' b) * b
    expand =
      trans
        (cong₂ _*_ (sym (divMod-law a b)) (sym (divMod-law a' b)))
        (shuffle (div a b) (mod a b) (div a' b) (mod a' b) b)
      where
        shuffle
          : ∀ p u q v w
          → (p * w + u) * (q * w + v) ≡ (u * v) + (p * q * w + p * v + u * q) * w
        shuffle = 
          solve
            5
            (λ p u q v w →
              ((p :* w) :+ u) :* ((q :* w) :+ v)
              := (u :* v) :+ (((p :* q :* w) :+ (p :* v) :+ (u :* q)) :* w)
            )
            refl
          where open +-*-Solver
```

## The partial denotations

The `Maybe`-valued denotations exported to Haskell from `Builtin.Integer.Base`
(and executed by the CEK machine via `Builtin.CInteger`) provably apply the
genuine operators on every non-zero divisor, and fail exactly on the zero
divisor. This is what makes the differential property tests in
`test-integer-division` tests of the real `quot`/`rem`/`div`/`mod`: the
wrapper layer is machine-checked to be transparent.

```
quotMaybe-correct
  : (n d : ℤ) (d≢0 : d ≢ 0ℤ)
  → quotMaybe n d ≡ just (quot n d {{≢-nonZero d≢0}})
quotMaybe-correct n d d≢0 with d ≟ 0ℤ
... | yes d≡0 = contradiction d≡0 d≢0
... | no _    = refl

remMaybe-correct
  : (n d : ℤ) (d≢0 : d ≢ 0ℤ)
  → remMaybe n d ≡ just (rem n d {{≢-nonZero d≢0}})
remMaybe-correct n d d≢0 with d ≟ 0ℤ
... | yes d≡0 = contradiction d≡0 d≢0
... | no _    = refl

divModMaybe-correct
  : (n d : ℤ) (d≢0 : d ≢ 0ℤ)
  → divModMaybe n d ≡ just (divMod n d {{≢-nonZero d≢0}})
divModMaybe-correct n d d≢0 with d ≟ 0ℤ
... | yes d≡0 = contradiction d≡0 d≢0
... | no _    = refl

divMaybe-correct
  : (n d : ℤ) (d≢0 : d ≢ 0ℤ)
  → divMaybe n d ≡ just (div n d {{≢-nonZero d≢0}})
divMaybe-correct n d d≢0 = cong (map proj₁) (divModMaybe-correct n d d≢0)

modMaybe-correct
  : (n d : ℤ) (d≢0 : d ≢ 0ℤ)
  → modMaybe n d ≡ just (mod n d {{≢-nonZero d≢0}})
modMaybe-correct n d d≢0 = cong (map proj₂) (divModMaybe-correct n d d≢0)
```

On the zero divisor, all the denotations fail by computation.

```
quotMaybe-zero : (n : ℤ) → quotMaybe n 0ℤ ≡ nothing
quotMaybe-zero n = refl

remMaybe-zero : (n : ℤ) → remMaybe n 0ℤ ≡ nothing
remMaybe-zero n = refl

divMaybe-zero : (n : ℤ) → divMaybe n 0ℤ ≡ nothing
divMaybe-zero n = refl

modMaybe-zero : (n : ℤ) → modMaybe n 0ℤ ≡ nothing
modMaybe-zero n = refl
```
