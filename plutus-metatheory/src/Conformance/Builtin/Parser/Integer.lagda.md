---
title: Conformance.Builtin.Parser.Integer
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/parser/integer`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Parser.Integer where

open import Conformance.Eval
```

## integer-01

```
-- builtin/parser/integer/integer-01
test-integer-01 : Untyped
test-integer-01 = (UCon (tagCon integer (ℤ.pos 0)))

expected-integer-01 : Result
expected-integer-01 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-integer-01 ≡ expected-integer-01
_ = refl
```

## integer-02

```
-- builtin/parser/integer/integer-02
test-integer-02 : Untyped
test-integer-02 = (UCon (tagCon integer (ℤ.pos 1)))

expected-integer-02 : Result
expected-integer-02 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-integer-02 ≡ expected-integer-02
_ = refl
```

## integer-03

```
-- builtin/parser/integer/integer-03
test-integer-03 : Untyped
test-integer-03 = (UCon (tagCon integer (ℤ.negsuc 0)))

expected-integer-03 : Result
expected-integer-03 = success (UCon (tagCon integer (ℤ.negsuc 0)))

_ : evalRaw test-integer-03 ≡ expected-integer-03
_ = refl
```

## integer-04

```
-- builtin/parser/integer/integer-04
test-integer-04 : Untyped
test-integer-04 = (UCon (tagCon integer (ℤ.pos 12345)))

expected-integer-04 : Result
expected-integer-04 = success (UCon (tagCon integer (ℤ.pos 12345)))

_ : evalRaw test-integer-04 ≡ expected-integer-04
_ = refl
```

## integer-05

```
-- builtin/parser/integer/integer-05
test-integer-05 : Untyped
test-integer-05 = (UCon (tagCon integer (ℤ.negsuc 12344)))

expected-integer-05 : Result
expected-integer-05 = success (UCon (tagCon integer (ℤ.negsuc 12344)))

_ : evalRaw test-integer-05 ≡ expected-integer-05
_ = refl
```

## integer-06

```
-- builtin/parser/integer/integer-06
test-integer-06 : Untyped
test-integer-06 = (UCon (tagCon integer (ℤ.pos 7934472584735297345829374203940389857324250374130461237461374324689198237413246172439813568362847918324132461234689173469172364972574327894626348923469234728574196241238723984567805163407561370166661807515263473485635726)))

expected-integer-06 : Result
expected-integer-06 = success (UCon (tagCon integer (ℤ.pos 7934472584735297345829374203940389857324250374130461237461374324689198237413246172439813568362847918324132461234689173469172364972574327894626348923469234728574196241238723984567805163407561370166661807515263473485635726)))

_ : evalRaw test-integer-06 ≡ expected-integer-06
_ = refl
```

## integer-07

```
-- builtin/parser/integer/integer-07
test-integer-07 : Untyped
test-integer-07 = (UCon (tagCon integer (ℤ.negsuc 7934472584735297345829374203940389857324250374130461237461374324689198237413246172439813568362847918324132461234689173469172364972574327894626348923469234728574196241238723984567805163407561370166661807515263473485635725)))

expected-integer-07 : Result
expected-integer-07 = success (UCon (tagCon integer (ℤ.negsuc 7934472584735297345829374203940389857324250374130461237461374324689198237413246172439813568362847918324132461234689173469172364972574327894626348923469234728574196241238723984567805163407561370166661807515263473485635725)))

_ : evalRaw test-integer-07 ≡ expected-integer-07
_ = refl
```

## integer-08

```
-- builtin/parser/integer/integer-08
test-integer-08 : Untyped
test-integer-08 = (UCon (tagCon integer (ℤ.pos 7934472584735297345829374203940389857324250374130461237461374324689198237413246172439813568362847918324132461234689173469172364972574327894626348923469234728574196241238723984567805163407561370166661807515263473485635726)))

expected-integer-08 : Result
expected-integer-08 = success (UCon (tagCon integer (ℤ.pos 7934472584735297345829374203940389857324250374130461237461374324689198237413246172439813568362847918324132461234689173469172364972574327894626348923469234728574196241238723984567805163407561370166661807515263473485635726)))

_ : evalRaw test-integer-08 ≡ expected-integer-08
_ = refl
```

## integer-09

Skipped: the program does not parse or has free variables (`parse/decode error`).

## integer10

Skipped: the program does not parse or has free variables (`parse/decode error`).
