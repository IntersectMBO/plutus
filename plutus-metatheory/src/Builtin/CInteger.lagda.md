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

The bounds are `-2^(2^18-1)` and `2^(2^18-1) - 1`.

The power is deliberately not written as `(+ 2) ^ (2 ℕ.^ 18 ∸ 1)`. The standard
library defines `_^_` by structural recursion on the exponent
(`x ^ suc n = x * x ^ n`), so normalising that expression takes 262143
multiplications of ever larger numbers. This is harmless in compiled code,
where GHC evaluates the constant once, but Agda's type checker does not cache
the normal form of a definition between uses.

`pow2pred n` instead computes `2^(2^n - 1)` by repeated squaring, using
`2^(2^(n+1) - 1) = 2 · (2^(2^n - 1))²`, so `pow2pred 18` normalises in 18
multiplications. The lemma `pow2pred-18` checks, by evaluating the direct
definition once, that the two agree.

```
pow2pred : ℕ → ℕ
pow2pred ℕ.zero    = 1
pow2pred (ℕ.suc n) = 2 ℕ.* pow2pred n ℕ.* pow2pred n

pow2pred-18 : pow2pred 18 ≡ 2 ℕ.^ (2 ℕ.^ 18 ∸ 1)
pow2pred-18 = refl

minBound : ℤ
minBound = - (+ pow2pred 18)
maxBound : ℤ
maxBound = (+ pow2pred 18) - (+ 1)

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