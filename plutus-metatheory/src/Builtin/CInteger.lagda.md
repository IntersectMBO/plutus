---
title: CInteger
layout: page
---

This module contains the formalisation of Cardano Integers.

```
module Builtin.CInteger where
```

## Imports

```
open import Data.Integer.Properties using (_<?_; _≤?_)
open import Relation.Nullary using (isYes)
open import Data.Integer.Base
open import Data.Nat.Base as ℕ using (ℕ;_∸_)
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
open import Data.Bool using (Bool)

```

## The CInteger type

The `CInteger` type is a restriction of the `ℤ` type to the range of integers specified by `minBound` and `maxBound`.

This type constitutes the denotational semantics of the Cardano `BuiltinInteger` type for all of the inputs to the `BuiltinInteger` builtin functions, except `equalsInteger` and `expModInteger`.

The inputs to `equalsInteger` are of the unrestricted `ℤ` type. The `expModInteger` function is not yet formalised and is left as future work.

```
minBound : ℤ
minBound = - ((+ 2) ^ (2 ℕ.^ 18 ∸ 1))
maxBound : ℤ
maxBound = ((+ 2) ^ (2 ℕ.^ 18 ∸ 1)) - (+ 1)

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

subtract : CInteger → CInteger → ℤ
subtract (cInt i _ _) (cInt j _ _) = i - j

multiply : CInteger → CInteger → ℤ
multiply (cInt i _ _) (cInt j _ _) = i * j

quot : CInteger → CInteger → Maybe ℤ
quot (cInt n _ _) (cInt d _ _) = Bℤ.quotMaybe n d

rem : CInteger → CInteger → Maybe ℤ
rem (cInt n _ _) (cInt d _ _) = Bℤ.remMaybe n d

divMod : CInteger → CInteger → Maybe (ℤ × ℤ)
divMod (cInt n _ _) (cInt d _ _) = Bℤ.divModMaybe n d

div : CInteger → CInteger → Maybe ℤ
div n d = map proj₁ (divMod n d)

mod : CInteger → CInteger → Maybe ℤ
mod n d = map proj₂ (divMod n d)

lessThan : CInteger → CInteger → Bool
lessThan (cInt i _ _) (cInt j _ _) = isYes (i <? j)

lessThanEquals : CInteger → CInteger → Bool
lessThanEquals (cInt i _ _) (cInt j _ _) = isYes (i ≤? j)
```