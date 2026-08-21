---
title: Builtin.Integer.Base
layout: page
---

This module contains the extra definitions for the ℤ type required for
the formalisation of Plutus Core builtins.

```
module Builtin.Integer.Base where
```

## Imports

```
open import Data.Integer
import Data.Nat as ℕ
import Data.Sign as S
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Relation.Nullary.Decidable using (yes; no)
```

## Quotient and remainder

The `quot` and `rem` functions are based on the Haskell `quot` and `rem` functions,
which perform truncated division.
This follows the implementation of Haskell's `integerQuotRem#`. 

```
quot : (n d : ℤ) .{{_ : NonZero d}} → ℤ
quot n d = (sign n S.* sign d) ◃ (∣ n ∣ ℕ./ ∣ d ∣)

rem : (n d : ℤ) .{{_ : NonZero d}} → ℤ
rem n d = sign n ◃ (∣ n ∣ ℕ.% ∣ d ∣)
```

## Division and modulus

The `div` and `mod` functions are based on Haskell's `div` and `mod`,
via the same fixup as `integerDivMod#`. This implements floored division.

```
divModFixup : (q r d : ℤ) → .{{_ : NonZero d}} → ℤ × ℤ
-- r > 0, d < 0
divModFixup q r@(+[1+ _ ]) d@(-[1+ _ ]) = (pred q , r + d)
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

## Partial denotations

The Plutus Core builtins fail on a zero divisor, so their denotations are the
`Maybe`-valued forms of the operators above: `nothing` when the divisor is
zero, otherwise the total function applied under the `NonZero` evidence
produced by the check. These are the functions the CEK machine executes (via
`Builtin.CInteger`); `Builtin.Integer.Properties` proves they agree with
`quot`/`rem`/`div`/`mod` on every non-zero divisor.

```
quotMaybe : ℤ → ℤ → Maybe ℤ
quotMaybe n d with d ≟ 0ℤ
... | yes _   = nothing
... | no d≢0  = just (quot n d)
  where instance _ = ≢-nonZero d≢0

remMaybe : ℤ → ℤ → Maybe ℤ
remMaybe n d with d ≟ 0ℤ
... | yes _   = nothing
... | no d≢0  = just (rem n d)
  where instance _ = ≢-nonZero d≢0

divModMaybe : ℤ → ℤ → Maybe (ℤ × ℤ)
divModMaybe n d with d ≟ 0ℤ
... | yes _   = nothing
... | no d≢0  = just (divMod n d)
  where instance _ = ≢-nonZero d≢0

divMaybe : ℤ → ℤ → Maybe ℤ
divMaybe n d = map proj₁ (divModMaybe n d)

modMaybe : ℤ → ℤ → Maybe ℤ
modMaybe n d = map proj₂ (divModMaybe n d)
```

The denotations are exported to Haskell under stable, readable names, so that
the compiled Agda implementation can be property-tested directly against
Haskell's `quot`/`rem`/`div`/`mod` (see the `test-integer-division` suite).

```
{-# COMPILE GHC quotMaybe as agdaQuotientInteger #-}
{-# COMPILE GHC remMaybe as agdaRemainderInteger #-}
{-# COMPILE GHC divMaybe as agdaDivideInteger #-}
{-# COMPILE GHC modMaybe as agdaModInteger #-}
```