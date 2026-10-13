---
title: Conformance.Builtin.Semantics.EqualsByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/equalsByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.EqualsByteString where

open import Conformance.Eval
```

## equalsByteString

```
-- builtin/semantics/equalsByteString/equalsByteString
test-equalsByteString : Untyped
test-equalsByteString = (UApp (UApp (UBuiltin equalsByteString) (UCon (tagCon bytestring (mkByteString "00ffaa")))) (UCon (tagCon bytestring (mkByteString "00ffaa"))))

expected-equalsByteString : Result
expected-equalsByteString = success (UCon (tagCon bool true))

_ : evalRaw test-equalsByteString ≡ expected-equalsByteString
_ = refl
```

## equalsByteString-01

```
-- builtin/semantics/equalsByteString/equalsByteString-01
test-equalsByteString-01 : Untyped
test-equalsByteString-01 = (UApp (UBuiltin lengthOfByteString) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))

expected-equalsByteString-01 : Result
expected-equalsByteString-01 = success (UCon (tagCon integer (ℤ.pos 13)))

_ : evalRaw test-equalsByteString-01 ≡ expected-equalsByteString-01
_ = refl
```

## equalsByteString-02

```
-- builtin/semantics/equalsByteString/equalsByteString-02
test-equalsByteString-02 : Untyped
test-equalsByteString-02 = (UApp (UApp (UBuiltin equalsByteString) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965")))) (UCon (tagCon bytestring (mkByteString "54686543616b65497341506965"))))

expected-equalsByteString-02 : Result
expected-equalsByteString-02 = success (UCon (tagCon bool false))

_ : evalRaw test-equalsByteString-02 ≡ expected-equalsByteString-02
_ = refl
```
