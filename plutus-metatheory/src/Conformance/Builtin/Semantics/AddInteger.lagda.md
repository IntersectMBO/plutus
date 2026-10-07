---
title: Conformance.Builtin.Semantics.AddInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/addInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.AddInteger where

open import Conformance.Eval
```

## addInteger-01

```
-- builtin/semantics/addInteger/addInteger-01
test-addInteger-01 : Untyped
test-addInteger-01 = (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1))))

expected-addInteger-01 : Result
expected-addInteger-01 = success (UCon (tagCon integer (ℤ.pos 2)))

_ : evalRaw test-addInteger-01 ≡ expected-addInteger-01
_ = refl
```

## addInteger-02

```
-- builtin/semantics/addInteger/addInteger-02
test-addInteger-02 : Untyped
test-addInteger-02 = (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.negsuc 1789345783478975892347952789341)))) (UCon (tagCon integer (ℤ.pos 5734))))

expected-addInteger-02 : Result
expected-addInteger-02 = success (UCon (tagCon integer (ℤ.negsuc 1789345783478975892347952783607)))

_ : evalRaw test-addInteger-02 ≡ expected-addInteger-02
_ = refl
```

## addInteger-03

```
-- builtin/semantics/addInteger/addInteger-03
test-addInteger-03 : Untyped
test-addInteger-03 = (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.negsuc 1789345783478975892347952789341)))) (UCon (tagCon integer (ℤ.pos 57347348957247358792345278346357234234527384258346526378567285925786235963258))))

expected-addInteger-03 : Result
expected-addInteger-03 = success (UCon (tagCon integer (ℤ.pos 57347348957247358792345278346357234234527384256557180595088310033438283173916)))

_ : evalRaw test-addInteger-03 ≡ expected-addInteger-03
_ = refl
```

## addInteger-04

```
-- builtin/semantics/addInteger/addInteger-04
test-addInteger-04 : Untyped
test-addInteger-04 = (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 7527934965792342535732746236582734865623578))))

expected-addInteger-04 : Result
expected-addInteger-04 = success (UCon (tagCon integer (ℤ.pos 7527934965792342535732746236582734865623578)))

_ : evalRaw test-addInteger-04 ≡ expected-addInteger-04
_ = refl
```

## addInteger-uncurried

```
-- builtin/semantics/addInteger/addInteger-uncurried
test-addInteger-uncurried : Untyped
test-addInteger-uncurried = (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))

expected-addInteger-uncurried : Result
expected-addInteger-uncurried = success (UCon (tagCon integer (ℤ.pos 3)))

_ : evalRaw test-addInteger-uncurried ≡ expected-addInteger-uncurried
_ = refl
```
