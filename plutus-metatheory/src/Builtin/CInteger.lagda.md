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
open import Data.Maybe.Properties using (≡-dec)
import Builtin.Integer.Base as Bℤ

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

quot : CInteger → CInteger → Maybe ℤ
quot (cInt n _ _) (cInt d _ _) with d ≟ + 0
... | yes _ = nothing
... | no d≢0 = just (Bℤ.quot n d)
  where instance
    _ = ≢-nonZero d≢0

rem : CInteger → CInteger → Maybe ℤ
rem (cInt n _ _) (cInt d _ _) with d ≟ + 0
... | yes _ = nothing
... | no d≢0 = just (Bℤ.rem n d)
  where instance
    _ = ≢-nonZero d≢0

divMod : CInteger → CInteger → Maybe (ℤ × ℤ)
divMod (cInt n _ _) (cInt d _ _) with d ≟ + 0
... | yes _ = nothing
... | no d≢0 = just (Bℤ.divMod n d)
  where instance
    _ = ≢-nonZero d≢0

div mod : CInteger → CInteger → Maybe ℤ
div n d = map proj₁ (divMod n d)
mod n d = map proj₂ (divMod n d)

-- TODO: theorems for impure div-mod and quot-rem, add a separate module 


```