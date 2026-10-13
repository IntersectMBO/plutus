---
title: Conformance.Builtin.Semantics.SliceByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/sliceByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.SliceByteString where

open import Conformance.Eval
```

## sliceByteString-01

```
-- builtin/semantics/sliceByteString/sliceByteString-01
test-sliceByteString-01 : Untyped
test-sliceByteString-01 = (UApp (UApp (UApp (UBuiltin sliceByteString) (UCon (tagCon integer (ℤ.pos 3)))) (UCon (tagCon integer (ℤ.pos 5)))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))

expected-sliceByteString-01 : Result
expected-sliceByteString-01 = success (UCon (tagCon bytestring (mkByteString "43616b6549")))

_ : evalRaw test-sliceByteString-01 ≡ expected-sliceByteString-01
_ = refl
```

## sliceByteString-02

```
-- builtin/semantics/sliceByteString/sliceByteString-02
test-sliceByteString-02 : Untyped
test-sliceByteString-02 = (UApp (UApp (UApp (UBuiltin sliceByteString) (UCon (tagCon integer (ℤ.negsuc 2)))) (UCon (tagCon integer (ℤ.pos 5)))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))

expected-sliceByteString-02 : Result
expected-sliceByteString-02 = success (UCon (tagCon bytestring (mkByteString "5468654361")))

_ : evalRaw test-sliceByteString-02 ≡ expected-sliceByteString-02
_ = refl
```

## sliceByteString-03

```
-- builtin/semantics/sliceByteString/sliceByteString-03
test-sliceByteString-03 : Untyped
test-sliceByteString-03 = (UApp (UApp (UApp (UBuiltin sliceByteString) (UCon (tagCon integer (ℤ.negsuc 2)))) (UCon (tagCon integer (ℤ.pos 1234)))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))

expected-sliceByteString-03 : Result
expected-sliceByteString-03 = success (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965")))

_ : evalRaw test-sliceByteString-03 ≡ expected-sliceByteString-03
_ = refl
```

## sliceByteString-04

```
-- builtin/semantics/sliceByteString/sliceByteString-04
test-sliceByteString-04 : Untyped
test-sliceByteString-04 = (UApp (UApp (UApp (UBuiltin sliceByteString) (UCon (tagCon integer (ℤ.pos 5)))) (UCon (tagCon integer (ℤ.pos 3)))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))

expected-sliceByteString-04 : Result
expected-sliceByteString-04 = success (UCon (tagCon bytestring (mkByteString "6b6549")))

_ : evalRaw test-sliceByteString-04 ≡ expected-sliceByteString-04
_ = refl
```

## sliceByteString-05

```
-- builtin/semantics/sliceByteString/sliceByteString-05
test-sliceByteString-05 : Untyped
test-sliceByteString-05 = (UApp (UApp (UApp (UBuiltin sliceByteString) (UCon (tagCon integer (ℤ.pos 123456789123456789)))) (UCon (tagCon integer (ℤ.pos 123456789123456789)))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))

expected-sliceByteString-05 : Result
expected-sliceByteString-05 = success (UCon (tagCon bytestring (mkByteString "")))

_ : evalRaw test-sliceByteString-05 ≡ expected-sliceByteString-05
_ = refl
```
