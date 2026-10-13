---
title: Conformance.Builtin.Semantics.ComplementByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/complementByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ComplementByteString where

open import Conformance.Eval
```

## case-01

```
-- builtin/semantics/complementByteString/case-01
test-case-01 : Untyped
test-case-01 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString ""))))

expected-case-01 : Result
expected-case-01 = success (UCon (tagCon bytestring (mkByteString "")))

_ : evalRaw test-case-01 ≡ expected-case-01
_ = refl
```

## case-02

```
-- builtin/semantics/complementByteString/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "0f"))))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon bytestring (mkByteString "f0")))

_ : evalRaw test-case-02 ≡ expected-case-02
_ = refl
```

## case-03

```
-- builtin/semantics/complementByteString/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "b00b"))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon bytestring (mkByteString "4ff4")))

_ : evalRaw test-case-03 ≡ expected-case-03
_ = refl
```

## case-04

```
-- builtin/semantics/complementByteString/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3"))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon bytestring (mkByteString "246379e3675c2e6346d73dd5cd5551f5b08bfeec23b78cb2c3ffe9a834702d46b68050e95bf3e1322829a7e4aa49daaac50c")))

_ : evalRaw test-case-04 ≡ expected-case-04
_ = refl
```

## case-05

```
-- builtin/semantics/complementByteString/case-05
test-case-05 : Untyped
test-case-05 = (UApp (ULambda (UApp (UApp (UBuiltin equalsByteString) (UVar 0)) (UApp (UBuiltin complementByteString) (UApp (UBuiltin complementByteString) (UVar 0))))) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3"))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bool true))

_ : evalRaw test-case-05 ≡ expected-case-05
_ = refl
```
