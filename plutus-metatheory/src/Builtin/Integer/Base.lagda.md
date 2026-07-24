---
title: Builtin.Integer.Base
layout: page
---

This module contains the extra definitions for the ℤ type required for the formalisation of Plutus Core builtins.

```
module Builtin.Integer.Base where
```

## Imports

```
open import Data.Integer
import Data.Nat as ℕ
import Data.Sign as S
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
```

## Quotient and remainder

The `quot` and `rem` functions are based on the Haskell `quot` and `rem` functions, which perform truncated division.
This follows the implementation of Haskell's `integerQuotRem#`. 

```
quot : (n d : ℤ) .{{_ : NonZero d}} → ℤ
quot n d = ((sign n S.* sign d) ◃ (∣ n ∣ ℕ./ ∣ d ∣))

rem : (n d : ℤ) .{{_ : NonZero d}} → ℤ
rem n d = sign n ◃ (∣ n ∣ ℕ.% ∣ d ∣)
```

## Division and modulus

The `div` and `mod` functions are based on Haskell's `div` and `mod`, via the same fixup as `integerDivMod#`. This implements floored division.

```
divModFixup : ℤ → ℤ → ℤ → ℤ × ℤ
-- r > 0, d < 0
divModFixup q r@(+ _) d@(-[1+ _ ]) = (pred q , r + d)
-- r < 0, d > 0
divModFixup q r@(-[1+ _ ]) d@(+ _) = (pred q , r + d)
-- r = 0 or same sign
divModFixup q r  d = (q , r)

divMod : (n d : ℤ) .{{_ : NonZero d}} → ℤ × ℤ
divMod n d = divModFixup (quot n d) (rem n d) d

div : (n d : ℤ) .{{_ : NonZero d}} → ℤ
div n d = proj₁ (divMod n d)

mod : (n d : ℤ) .{{_ : NonZero d}} → ℤ
mod n d = proj₂ (divMod n d)
```