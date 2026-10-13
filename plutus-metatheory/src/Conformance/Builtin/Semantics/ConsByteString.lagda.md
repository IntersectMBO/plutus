---
title: Conformance.Builtin.Semantics.ConsByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/consByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ConsByteString where

open import Conformance.Eval
```

## consByteString-01

```
-- builtin/semantics/consByteString/consByteString-01
-- the arg overflow'ed over the maxBound :: Word8
test-consByteString-01 : Untyped
test-consByteString-01 = (UApp (UApp (UBuiltin consByteString) (UCon (tagCon integer (ℤ.pos 256)))) (UCon (tagCon bytestring (mkByteString ""))))

expected-consByteString-01 : Result
expected-consByteString-01 = failure

_ : evalRaw test-consByteString-01 ≡ expected-consByteString-01
_ = refl
```

## consByteString-02

```
-- builtin/semantics/consByteString/consByteString-02
test-consByteString-02 : Untyped
test-consByteString-02 = (UApp (UApp (UBuiltin consByteString) (UCon (tagCon integer (ℤ.negsuc 87)))) (UCon (tagCon bytestring (mkByteString "686543616b654973414c6965"))))

expected-consByteString-02 : Result
expected-consByteString-02 = failure

_ : evalRaw test-consByteString-02 ≡ expected-consByteString-02
_ = refl
```

## consByteString-03

```
-- builtin/semantics/consByteString/consByteString-03
test-consByteString-03 : Untyped
test-consByteString-03 = (UApp (UApp (UBuiltin consByteString) (UCon (tagCon integer (ℤ.pos 84)))) (UCon (tagCon bytestring (mkByteString "686543616b654973414c6965"))))

expected-consByteString-03 : Result
expected-consByteString-03 = success (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965")))

_ : evalRaw test-consByteString-03 ≡ expected-consByteString-03
_ = refl
```
