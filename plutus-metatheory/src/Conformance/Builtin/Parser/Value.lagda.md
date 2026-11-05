---
title: Conformance.Builtin.Parser.Value
layout: page
---

<!-- GENERATED FILE: do not edit.
<<<<<<< HEAD
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
=======
     Regenerate with `generate-agda-typecheck-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-typecheck-conformance` from the
>>>>>>> origin/master
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/parser/value`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Parser.Value where

open import Conformance.Eval
```

## currencyID-too-long-1

Skipped: the program does not parse or has free variables (`parse/decode error`).

## currencyID-too-long-2

Skipped: the program does not parse or has free variables (`parse/decode error`).

## currencyIDs-unordered

Skipped: the program does not parse or has free variables (`parse/decode error`).

## duplicate-currencyIDs

Skipped: the program does not parse or has free variables (`parse/decode error`).

## duplicate-tokenIDs

Skipped: the program does not parse or has free variables (`parse/decode error`).

## empty-tokens

Skipped: the program does not parse or has free variables (`parse/decode error`).

## empty-value

```
-- builtin/parser/value/empty-value
test-empty-value : Untyped
test-empty-value = (UCon (tagCon value (valueFromList ([]))))

expected-empty-value : Result
expected-empty-value = success (UCon (tagCon value (valueFromList ([]))))

-- Pending: value constant.
pending-empty-value : Set
pending-empty-value = Pending (evalRaw test-empty-value ≡ expected-empty-value)
```

## ill-formed

Skipped: the program does not parse or has free variables (`parse/decode error`).

## max-currencyID-length

```
-- builtin/parser/value/max-currencyID-length
test-max-currencyID-length : Untyped
<<<<<<< HEAD
test-max-currencyID-length = (UCon (tagCon value (valueFromList (((mkByteString "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") , (((mkByteString "") , (ℤ.pos 123)) ∷ ((mkByteString "00") , (ℤ.pos 456)) ∷ [])) ∷ []))))

expected-max-currencyID-length : Result
expected-max-currencyID-length = success (UCon (tagCon value (valueFromList (((mkByteString "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") , (((mkByteString "") , (ℤ.pos 123)) ∷ ((mkByteString "00") , (ℤ.pos 456)) ∷ [])) ∷ []))))
=======
test-max-currencyID-length = (UCon (tagCon value (valueFromList (((mkByteString "\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170") , (((mkByteString "") , (ℤ.pos 123)) ∷ ((mkByteString "\NUL") , (ℤ.pos 456)) ∷ [])) ∷ []))))

expected-max-currencyID-length : Result
expected-max-currencyID-length = success (UCon (tagCon value (valueFromList (((mkByteString "\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170") , (((mkByteString "") , (ℤ.pos 123)) ∷ ((mkByteString "\NUL") , (ℤ.pos 456)) ∷ [])) ∷ []))))
>>>>>>> origin/master

-- Pending: value constant.
pending-max-currencyID-length : Set
pending-max-currencyID-length = Pending (evalRaw test-max-currencyID-length ≡ expected-max-currencyID-length)
```

## max-tokenID-length

```
-- builtin/parser/value/max-tokenID-length
test-max-tokenID-length : Untyped
<<<<<<< HEAD
test-max-tokenID-length = (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "1234") , (ℤ.pos 456)) ∷ ((mkByteString "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") , (ℤ.pos 123)) ∷ [])) ∷ []))))

expected-max-tokenID-length : Result
expected-max-tokenID-length = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "1234") , (ℤ.pos 456)) ∷ ((mkByteString "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") , (ℤ.pos 123)) ∷ [])) ∷ []))))
=======
test-max-tokenID-length = (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "\DC24") , (ℤ.pos 456)) ∷ ((mkByteString "\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170") , (ℤ.pos 123)) ∷ [])) ∷ []))))

expected-max-tokenID-length : Result
expected-max-tokenID-length = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "\DC24") , (ℤ.pos 456)) ∷ ((mkByteString "\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170") , (ℤ.pos 123)) ∷ [])) ∷ []))))
>>>>>>> origin/master

-- Pending: value constant.
pending-max-tokenID-length : Set
pending-max-tokenID-length = Pending (evalRaw test-max-tokenID-length ≡ expected-max-tokenID-length)
```

## no-overflow

```
-- builtin/parser/value/no-overflow
test-no-overflow : Untyped
test-no-overflow = (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))

expected-no-overflow : Result
expected-no-overflow = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))

-- Pending: value constant.
pending-no-overflow : Set
pending-no-overflow = Pending (evalRaw test-no-overflow ≡ expected-no-overflow)
```

## no-underflow

```
-- builtin/parser/value/no-underflow
test-no-underflow : Untyped
test-no-underflow = (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))

expected-no-underflow : Result
expected-no-underflow = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))

-- Pending: value constant.
pending-no-underflow : Set
pending-no-underflow = Pending (evalRaw test-no-underflow ≡ expected-no-underflow)
```

## overflow

Skipped: the program does not parse or has free variables (`parse/decode error`).

## tokenID-too-long-1

Skipped: the program does not parse or has free variables (`parse/decode error`).

## tokenID-too-long-2

Skipped: the program does not parse or has free variables (`parse/decode error`).

## tokenIDs-unordered

Skipped: the program does not parse or has free variables (`parse/decode error`).

## underflow

Skipped: the program does not parse or has free variables (`parse/decode error`).

## value-ok-1

```
-- builtin/parser/value/value-ok-1
test-value-ok-1 : Untyped
<<<<<<< HEAD
test-value-ok-1 = (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 123)) ∷ ((mkByteString "bb") , (ℤ.pos 50000)) ∷ [])) ∷ ((mkByteString "ffff") , (((mkByteString "aa") , (ℤ.negsuc 9)) ∷ ((mkByteString "bb") , (ℤ.pos 20)) ∷ [])) ∷ []))))

expected-value-ok-1 : Result
expected-value-ok-1 = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 123)) ∷ ((mkByteString "bb") , (ℤ.pos 50000)) ∷ [])) ∷ ((mkByteString "ffff") , (((mkByteString "aa") , (ℤ.negsuc 9)) ∷ ((mkByteString "bb") , (ℤ.pos 20)) ∷ [])) ∷ []))))
=======
test-value-ok-1 = (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 123)) ∷ ((mkByteString "\187") , (ℤ.pos 50000)) ∷ [])) ∷ ((mkByteString "\255\255") , (((mkByteString "\170") , (ℤ.negsuc 9)) ∷ ((mkByteString "\187") , (ℤ.pos 20)) ∷ [])) ∷ []))))

expected-value-ok-1 : Result
expected-value-ok-1 = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 123)) ∷ ((mkByteString "\187") , (ℤ.pos 50000)) ∷ [])) ∷ ((mkByteString "\255\255") , (((mkByteString "\170") , (ℤ.negsuc 9)) ∷ ((mkByteString "\187") , (ℤ.pos 20)) ∷ [])) ∷ []))))
>>>>>>> origin/master

-- Pending: value constant.
pending-value-ok-1 : Set
pending-value-ok-1 = Pending (evalRaw test-value-ok-1 ≡ expected-value-ok-1)
```

## value-ok-2

```
-- builtin/parser/value/value-ok-2
-- Complex value
test-value-ok-2 : Untyped
<<<<<<< HEAD
test-value-ok-2 = (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "11") , (ℤ.pos 11)) ∷ ((mkByteString "22") , (ℤ.pos 22)) ∷ ((mkByteString "33") , (ℤ.pos 33)) ∷ ((mkByteString "4567") , (ℤ.pos 4567)) ∷ ((mkByteString "ff") , (ℤ.negsuc 3)) ∷ [])) ∷ ((mkByteString "00") , (((mkByteString "") , (ℤ.pos 5)) ∷ ((mkByteString "00") , (ℤ.pos 1)) ∷ ((mkByteString "0000") , (ℤ.negsuc 7)) ∷ ((mkByteString "0000000000000000") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "0000") , (((mkByteString "00") , (ℤ.pos 1)) ∷ ((mkByteString "0000000000000000") , (ℤ.pos 44)) ∷ ((mkByteString "0001") , (ℤ.negsuc 7)) ∷ ((mkByteString "02") , (ℤ.pos 4)) ∷ [])) ∷ ((mkByteString "000000") , (((mkByteString "00") , (ℤ.pos 11111)) ∷ ((mkByteString "1111") , (ℤ.negsuc 8237894781)) ∷ ((mkByteString "111111111111") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "00000000") , (((mkByteString "00") , (ℤ.pos 27893471)) ∷ ((mkByteString "0000") , (ℤ.negsuc 7)) ∷ ((mkByteString "0000000000000000") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "000001") , (((mkByteString "00") , (ℤ.pos 1)) ∷ ((mkByteString "0000") , (ℤ.pos 44)) ∷ ((mkByteString "0000000000000000") , (ℤ.pos 44)) ∷ ((mkByteString "00000d") , (ℤ.pos 33)) ∷ [])) ∷ ((mkByteString "11") , (((mkByteString "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ ((mkByteString "d0") , (ℤ.negsuc 22234789728934789237492734789237893)) ∷ [])) ∷ ((mkByteString "2299ffff4321") , (((mkByteString "aa") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "3333") , (((mkByteString "000000000000000d00") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "34") , (((mkByteString "aa") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "400000003945237890542789034cab") , (((mkByteString "11") , (ℤ.pos 12345)) ∷ [])) ∷ ((mkByteString "49fc93aa802378974ffffffffffff3") , (((mkByteString "12") , (ℤ.pos 54321)) ∷ [])) ∷ ((mkByteString "ff00000000000000000000000000000000000000000000000000000000000000") , (((mkByteString "0000000000000000000000000000000000000000000000000000000000000000") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ ((mkByteString "ff000000000000000000000000000000000000000000000000000000000001") , (((mkByteString "") , (ℤ.pos 7)) ∷ ((mkByteString "21789789af879737489f94b562138877c52a6728463784678909eeeeeeeeeeee") , (ℤ.pos 17)) ∷ ((mkByteString "21789789af879737489f94b562138877c52a6728463784678909eeeeeeeeeeef") , (ℤ.negsuc 16)) ∷ ((mkByteString "42378942") , (ℤ.pos 128389712378911)) ∷ [])) ∷ ((mkByteString "ff9274b2a893") , (((mkByteString "") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ ((mkByteString "01") , (ℤ.pos 1)) ∷ ((mkByteString "11") , (ℤ.pos 2)) ∷ [])) ∷ []))))

expected-value-ok-2 : Result
expected-value-ok-2 = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "11") , (ℤ.pos 11)) ∷ ((mkByteString "22") , (ℤ.pos 22)) ∷ ((mkByteString "33") , (ℤ.pos 33)) ∷ ((mkByteString "4567") , (ℤ.pos 4567)) ∷ ((mkByteString "ff") , (ℤ.negsuc 3)) ∷ [])) ∷ ((mkByteString "00") , (((mkByteString "") , (ℤ.pos 5)) ∷ ((mkByteString "00") , (ℤ.pos 1)) ∷ ((mkByteString "0000") , (ℤ.negsuc 7)) ∷ ((mkByteString "0000000000000000") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "0000") , (((mkByteString "00") , (ℤ.pos 1)) ∷ ((mkByteString "0000000000000000") , (ℤ.pos 44)) ∷ ((mkByteString "0001") , (ℤ.negsuc 7)) ∷ ((mkByteString "02") , (ℤ.pos 4)) ∷ [])) ∷ ((mkByteString "000000") , (((mkByteString "00") , (ℤ.pos 11111)) ∷ ((mkByteString "1111") , (ℤ.negsuc 8237894781)) ∷ ((mkByteString "111111111111") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "00000000") , (((mkByteString "00") , (ℤ.pos 27893471)) ∷ ((mkByteString "0000") , (ℤ.negsuc 7)) ∷ ((mkByteString "0000000000000000") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "000001") , (((mkByteString "00") , (ℤ.pos 1)) ∷ ((mkByteString "0000") , (ℤ.pos 44)) ∷ ((mkByteString "0000000000000000") , (ℤ.pos 44)) ∷ ((mkByteString "00000d") , (ℤ.pos 33)) ∷ [])) ∷ ((mkByteString "11") , (((mkByteString "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ ((mkByteString "d0") , (ℤ.negsuc 22234789728934789237492734789237893)) ∷ [])) ∷ ((mkByteString "2299ffff4321") , (((mkByteString "aa") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "3333") , (((mkByteString "000000000000000d00") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "34") , (((mkByteString "aa") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "400000003945237890542789034cab") , (((mkByteString "11") , (ℤ.pos 12345)) ∷ [])) ∷ ((mkByteString "49fc93aa802378974ffffffffffff3") , (((mkByteString "12") , (ℤ.pos 54321)) ∷ [])) ∷ ((mkByteString "ff00000000000000000000000000000000000000000000000000000000000000") , (((mkByteString "0000000000000000000000000000000000000000000000000000000000000000") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ ((mkByteString "ff000000000000000000000000000000000000000000000000000000000001") , (((mkByteString "") , (ℤ.pos 7)) ∷ ((mkByteString "21789789af879737489f94b562138877c52a6728463784678909eeeeeeeeeeee") , (ℤ.pos 17)) ∷ ((mkByteString "21789789af879737489f94b562138877c52a6728463784678909eeeeeeeeeeef") , (ℤ.negsuc 16)) ∷ ((mkByteString "42378942") , (ℤ.pos 128389712378911)) ∷ [])) ∷ ((mkByteString "ff9274b2a893") , (((mkByteString "") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ ((mkByteString "01") , (ℤ.pos 1)) ∷ ((mkByteString "11") , (ℤ.pos 2)) ∷ [])) ∷ []))))
=======
test-value-ok-2 = (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "\DC1") , (ℤ.pos 11)) ∷ ((mkByteString "\"") , (ℤ.pos 22)) ∷ ((mkByteString "3") , (ℤ.pos 33)) ∷ ((mkByteString "Eg") , (ℤ.pos 4567)) ∷ ((mkByteString "\255") , (ℤ.negsuc 3)) ∷ [])) ∷ ((mkByteString "\NUL") , (((mkByteString "") , (ℤ.pos 5)) ∷ ((mkByteString "\NUL") , (ℤ.pos 1)) ∷ ((mkByteString "\NUL\NUL") , (ℤ.negsuc 7)) ∷ ((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "\NUL\NUL") , (((mkByteString "\NUL") , (ℤ.pos 1)) ∷ ((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.pos 44)) ∷ ((mkByteString "\NUL\SOH") , (ℤ.negsuc 7)) ∷ ((mkByteString "\STX") , (ℤ.pos 4)) ∷ [])) ∷ ((mkByteString "\NUL\NUL\NUL") , (((mkByteString "\NUL") , (ℤ.pos 11111)) ∷ ((mkByteString "\DC1\DC1") , (ℤ.negsuc 8237894781)) ∷ ((mkByteString "\DC1\DC1\DC1\DC1\DC1\DC1") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "\NUL\NUL\NUL\NUL") , (((mkByteString "\NUL") , (ℤ.pos 27893471)) ∷ ((mkByteString "\NUL\NUL") , (ℤ.negsuc 7)) ∷ ((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "\NUL\NUL\SOH") , (((mkByteString "\NUL") , (ℤ.pos 1)) ∷ ((mkByteString "\NUL\NUL") , (ℤ.pos 44)) ∷ ((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.pos 44)) ∷ ((mkByteString "\NUL\NUL\r") , (ℤ.pos 33)) ∷ [])) ∷ ((mkByteString "\DC1") , (((mkByteString "\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ ((mkByteString "\208") , (ℤ.negsuc 22234789728934789237492734789237893)) ∷ [])) ∷ ((mkByteString "\"\153\255\255C!") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "33") , (((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\r\NUL") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "4") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "@\NUL\NUL\NUL9E#x\144T'\137\ETXL\171") , (((mkByteString "\DC1") , (ℤ.pos 12345)) ∷ [])) ∷ ((mkByteString "I\252\147\170\128#x\151O\255\255\255\255\255\243") , (((mkByteString "\DC2") , (ℤ.pos 54321)) ∷ [])) ∷ ((mkByteString "\255\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ ((mkByteString "\255\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\SOH") , (((mkByteString "") , (ℤ.pos 7)) ∷ ((mkByteString "!x\151\137\175\135\151\&7H\159\148\181b\DC3\136w\197*g(F7\132g\137\t\238\238\238\238\238\238") , (ℤ.pos 17)) ∷ ((mkByteString "!x\151\137\175\135\151\&7H\159\148\181b\DC3\136w\197*g(F7\132g\137\t\238\238\238\238\238\239") , (ℤ.negsuc 16)) ∷ ((mkByteString "B7\137B") , (ℤ.pos 128389712378911)) ∷ [])) ∷ ((mkByteString "\255\146t\178\168\147") , (((mkByteString "") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ ((mkByteString "\SOH") , (ℤ.pos 1)) ∷ ((mkByteString "\DC1") , (ℤ.pos 2)) ∷ [])) ∷ []))))

expected-value-ok-2 : Result
expected-value-ok-2 = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "\DC1") , (ℤ.pos 11)) ∷ ((mkByteString "\"") , (ℤ.pos 22)) ∷ ((mkByteString "3") , (ℤ.pos 33)) ∷ ((mkByteString "Eg") , (ℤ.pos 4567)) ∷ ((mkByteString "\255") , (ℤ.negsuc 3)) ∷ [])) ∷ ((mkByteString "\NUL") , (((mkByteString "") , (ℤ.pos 5)) ∷ ((mkByteString "\NUL") , (ℤ.pos 1)) ∷ ((mkByteString "\NUL\NUL") , (ℤ.negsuc 7)) ∷ ((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "\NUL\NUL") , (((mkByteString "\NUL") , (ℤ.pos 1)) ∷ ((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.pos 44)) ∷ ((mkByteString "\NUL\SOH") , (ℤ.negsuc 7)) ∷ ((mkByteString "\STX") , (ℤ.pos 4)) ∷ [])) ∷ ((mkByteString "\NUL\NUL\NUL") , (((mkByteString "\NUL") , (ℤ.pos 11111)) ∷ ((mkByteString "\DC1\DC1") , (ℤ.negsuc 8237894781)) ∷ ((mkByteString "\DC1\DC1\DC1\DC1\DC1\DC1") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "\NUL\NUL\NUL\NUL") , (((mkByteString "\NUL") , (ℤ.pos 27893471)) ∷ ((mkByteString "\NUL\NUL") , (ℤ.negsuc 7)) ∷ ((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.pos 44)) ∷ [])) ∷ ((mkByteString "\NUL\NUL\SOH") , (((mkByteString "\NUL") , (ℤ.pos 1)) ∷ ((mkByteString "\NUL\NUL") , (ℤ.pos 44)) ∷ ((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.pos 44)) ∷ ((mkByteString "\NUL\NUL\r") , (ℤ.pos 33)) ∷ [])) ∷ ((mkByteString "\DC1") , (((mkByteString "\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204\204") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ ((mkByteString "\208") , (ℤ.negsuc 22234789728934789237492734789237893)) ∷ [])) ∷ ((mkByteString "\"\153\255\255C!") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "33") , (((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\r\NUL") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "4") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "@\NUL\NUL\NUL9E#x\144T'\137\ETXL\171") , (((mkByteString "\DC1") , (ℤ.pos 12345)) ∷ [])) ∷ ((mkByteString "I\252\147\170\128#x\151O\255\255\255\255\255\243") , (((mkByteString "\DC2") , (ℤ.pos 54321)) ∷ [])) ∷ ((mkByteString "\255\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ ((mkByteString "\255\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\SOH") , (((mkByteString "") , (ℤ.pos 7)) ∷ ((mkByteString "!x\151\137\175\135\151\&7H\159\148\181b\DC3\136w\197*g(F7\132g\137\t\238\238\238\238\238\238") , (ℤ.pos 17)) ∷ ((mkByteString "!x\151\137\175\135\151\&7H\159\148\181b\DC3\136w\197*g(F7\132g\137\t\238\238\238\238\238\239") , (ℤ.negsuc 16)) ∷ ((mkByteString "B7\137B") , (ℤ.pos 128389712378911)) ∷ [])) ∷ ((mkByteString "\255\146t\178\168\147") , (((mkByteString "") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ ((mkByteString "\SOH") , (ℤ.pos 1)) ∷ ((mkByteString "\DC1") , (ℤ.pos 2)) ∷ [])) ∷ []))))
>>>>>>> origin/master

-- Pending: value constant.
pending-value-ok-2 : Set
pending-value-ok-2 = Pending (evalRaw test-value-ok-2 ≡ expected-value-ok-2)
```

## zero-asset

Skipped: the program does not parse or has free variables (`parse/decode error`).
