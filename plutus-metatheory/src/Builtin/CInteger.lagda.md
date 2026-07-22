---
title: CInteger
layout: page
---

This module contains the formalisation of CIntegers.

```
module Builtin.CInteger where
```

## Imports

```
open import Data.Integer.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Integer.Base
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Sign.Base as S using (Sign)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing; map)
import Data.Maybe.Effectful as MaybeEff
open import Effect.Monad using (RawMonad)
import Agda.Primitive as Level
open RawMonad {f = Level.lzero} MaybeEff.monad
open import Relation.Binary.PropositionalEquality 

```

## The CInteger type

```
private
  minBound : ℤ
  minBound = - ((+ 2) ^ 262143)
  maxBound : ℤ
  maxBound = ((+ 2) ^ 262143) - (+ 1)

data CInteger : Set where
  cInt
    : (i : ℤ)
    → i ≥ minBound
    → i ≤ maxBound
    → CInteger
```

## CInteger operations

```
add : CInteger → CInteger → ℤ
add (cInt i _ _) (cInt j _ _) = i + j

substract : CInteger → CInteger → ℤ
substract (cInt i _ _) (cInt j _ _) = i - j

multiply : CInteger → CInteger → ℤ
multiply (cInt i _ _) (cInt j _ _) = i * j

-- Truncated division (Haskell quot/rem):
-- magnitudes divided in ℕ, signs fixed up exactly as integerQuotRem# does.

quot : CInteger → CInteger → Maybe ℤ
quot (cInt n _ _) (cInt d _ _) with d ≟ + 0
... | yes _ = nothing
... | no d≢0 = just ((sign n S.* sign d) ◃ (∣ n ∣ ℕ./ ∣ d ∣))
  where instance
    _ = ≢-nonZero d≢0

rem : CInteger → CInteger → Maybe ℤ
rem (cInt n _ _) (cInt d _ _) with d ≟ + 0
... | yes _ = nothing
... | no d≢0 = just (sign n ◃ (∣ n ∣ ℕ.% ∣ d ∣))
  where instance
    _ = ≢-nonZero d≢0

-- Floored division (Haskell div/mod), via the same fixup as integerDivMod#:
-- if r ≠ 0 and sign r ≠ sign d then (q-1, r+d) else (q, r).

divMod : CInteger → CInteger → Maybe (ℤ × ℤ)
divMod n d@(cInt di _ _) = do
    q ← quot n d
    r ← rem n d
    return (fixup q r di)
  where
    fixup : ℤ → ℤ → ℤ → ℤ × ℤ
    -- r > 0, d < 0
    fixup q r@(+ _) -[1+ _ ] =
      (pred q , r + di)   
    -- r < 0, d > 0
    fixup q r@(-[1+ _ ]) (+ _) =
      (pred q , r + di)   
    -- r = 0 or same sign
    fixup q r _ =
      (q , r)             

div mod : CInteger → CInteger → Maybe ℤ
div n d = map proj₁ (divMod n d)
mod n d = map proj₂ (divMod n d)

-- TODO:
-- quotRem-law : (x y : CInteger) → (quot x y) * y + (rem x y) ≡ x
-- divMod-law : (x y : CInteger) → (div x y) * y + (mod x y) ≡ x
-- other properties?

```