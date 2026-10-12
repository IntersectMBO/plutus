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
test-equalsByteString = (UApp (UApp (UBuiltin equalsByteString) (UCon (tagCon bytestring (mkByteString "\NUL\255\170")))) (UCon (tagCon bytestring (mkByteString "\NUL\255\170"))))

expected-equalsByteString : Result
expected-equalsByteString = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`.
pending-equalsByteString : Set
pending-equalsByteString = Pending (evalRaw test-equalsByteString ≡ expected-equalsByteString)
```

## equalsByteString-01

```
-- builtin/semantics/equalsByteString/equalsByteString-01
test-equalsByteString-01 : Untyped
test-equalsByteString-01 = (UApp (UBuiltin lengthOfByteString) (UCon (tagCon bytestring (mkByteString "TheCakeIsALie"))))

expected-equalsByteString-01 : Result
expected-equalsByteString-01 = success (UCon (tagCon integer (ℤ.pos 13)))

-- Pending: bytestring constant; postulated builtin `lengthOfByteString`.
pending-equalsByteString-01 : Set
pending-equalsByteString-01 = Pending (evalRaw test-equalsByteString-01 ≡ expected-equalsByteString-01)
```

## equalsByteString-02

```
-- builtin/semantics/equalsByteString/equalsByteString-02
test-equalsByteString-02 : Untyped
test-equalsByteString-02 = (UApp (UApp (UBuiltin equalsByteString) (UCon (tagCon bytestring (mkByteString "TheCakeIsALie")))) (UCon (tagCon bytestring (mkByteString "TheCakeIsAPie"))))

expected-equalsByteString-02 : Result
expected-equalsByteString-02 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `equalsByteString`.
pending-equalsByteString-02 : Set
pending-equalsByteString-02 = Pending (evalRaw test-equalsByteString-02 ≡ expected-equalsByteString-02)
```
