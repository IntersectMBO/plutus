---
title: Conformance.Builtin.Semantics.LessThanByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/lessThanByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.LessThanByteString where

open import Conformance.Eval
```

## lessThanByteString-00

```
-- builtin/semantics/lessThanByteString/lessThanByteString-00
test-lessThanByteString-00 : Untyped
test-lessThanByteString-00 = (UApp (UApp (UBuiltin lessThanByteString) (UCon (tagCon bytestring (mkByteString "00ff")))) (UCon (tagCon bytestring (mkByteString "00ffaa"))))

expected-lessThanByteString-00 : Result
expected-lessThanByteString-00 = success (UCon (tagCon bool true))

_ : evalRaw test-lessThanByteString-00 ≡ expected-lessThanByteString-00
_ = refl
```

## lessThanByteString-01

```
-- builtin/semantics/lessThanByteString/lessThanByteString-01
test-lessThanByteString-01 : Untyped
test-lessThanByteString-01 = (UApp (UApp (UBuiltin equalsByteString) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965")))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))

expected-lessThanByteString-01 : Result
expected-lessThanByteString-01 = success (UCon (tagCon bool true))

_ : evalRaw test-lessThanByteString-01 ≡ expected-lessThanByteString-01
_ = refl
```

## lessThanByteString-02

```
-- builtin/semantics/lessThanByteString/lessThanByteString-02
test-lessThanByteString-02 : Untyped
test-lessThanByteString-02 = (UApp (UApp (UBuiltin lessThanByteString) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965")))) (UCon (tagCon bytestring (mkByteString "54686543616b65497341506965"))))

expected-lessThanByteString-02 : Result
expected-lessThanByteString-02 = success (UCon (tagCon bool true))

_ : evalRaw test-lessThanByteString-02 ≡ expected-lessThanByteString-02
_ = refl
```

## lessThanByteString-03

```
-- builtin/semantics/lessThanByteString/lessThanByteString-03
test-lessThanByteString-03 : Untyped
test-lessThanByteString-03 = (UApp (UApp (UBuiltin lessThanByteString) (UCon (tagCon bytestring (mkByteString "54686543616b65497341506965")))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))

expected-lessThanByteString-03 : Result
expected-lessThanByteString-03 = success (UCon (tagCon bool false))

_ : evalRaw test-lessThanByteString-03 ≡ expected-lessThanByteString-03
_ = refl
```

## lessThanByteString-04

```
-- builtin/semantics/lessThanByteString/lessThanByteString-04
test-lessThanByteString-04 : Untyped
test-lessThanByteString-04 = (UApp (UApp (UBuiltin lessThanByteString) (UCon (tagCon bytestring (mkByteString "54686543616b65497341506965")))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c69"))))

expected-lessThanByteString-04 : Result
expected-lessThanByteString-04 = success (UCon (tagCon bool false))

_ : evalRaw test-lessThanByteString-04 ≡ expected-lessThanByteString-04
_ = refl
```

## lessThanByteString-05

```
-- builtin/semantics/lessThanByteString/lessThanByteString-05
test-lessThanByteString-05 : Untyped
test-lessThanByteString-05 = (UApp (UApp (UBuiltin lessThanByteString) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c69")))) (UCon (tagCon bytestring (mkByteString "54686543616b65497341506965"))))

expected-lessThanByteString-05 : Result
expected-lessThanByteString-05 = success (UCon (tagCon bool true))

_ : evalRaw test-lessThanByteString-05 ≡ expected-lessThanByteString-05
_ = refl
```
