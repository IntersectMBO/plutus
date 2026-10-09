---
title: Conformance.Builtin.Semantics.LessThanEqualsByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/lessThanEqualsByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.LessThanEqualsByteString where

open import Conformance.Eval
```

## lessThanEqualsByteString-00

```
-- builtin/semantics/lessThanEqualsByteString/lessThanEqualsByteString-00
test-lessThanEqualsByteString-00 : Untyped
test-lessThanEqualsByteString-00 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "\NUL\255")))) (UCon (tagCon bytestring (mkByteString "\NUL"))))

expected-lessThanEqualsByteString-00 : Result
expected-lessThanEqualsByteString-00 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `lessThanEqualsByteString`.
pending-lessThanEqualsByteString-00 : Set
pending-lessThanEqualsByteString-00 = Pending (evalRaw test-lessThanEqualsByteString-00 ≡ expected-lessThanEqualsByteString-00)
```

## lessThanEqualsByteString-01

```
-- builtin/semantics/lessThanEqualsByteString/lessThanEqualsByteString-01
test-lessThanEqualsByteString-01 : Untyped
test-lessThanEqualsByteString-01 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "TheCakeIsALid")))) (UCon (tagCon bytestring (mkByteString "TheCakeIsALie"))))

expected-lessThanEqualsByteString-01 : Result
expected-lessThanEqualsByteString-01 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `lessThanEqualsByteString`.
pending-lessThanEqualsByteString-01 : Set
pending-lessThanEqualsByteString-01 = Pending (evalRaw test-lessThanEqualsByteString-01 ≡ expected-lessThanEqualsByteString-01)
```

## lessThanEqualsByteString-02

```
-- builtin/semantics/lessThanEqualsByteString/lessThanEqualsByteString-02
test-lessThanEqualsByteString-02 : Untyped
test-lessThanEqualsByteString-02 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "TheCakeIsALif")))) (UCon (tagCon bytestring (mkByteString "TheCakeIsALie"))))

expected-lessThanEqualsByteString-02 : Result
expected-lessThanEqualsByteString-02 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `lessThanEqualsByteString`.
pending-lessThanEqualsByteString-02 : Set
pending-lessThanEqualsByteString-02 = Pending (evalRaw test-lessThanEqualsByteString-02 ≡ expected-lessThanEqualsByteString-02)
```

## lessThanEqualsByteString-03

```
-- builtin/semantics/lessThanEqualsByteString/lessThanEqualsByteString-03
test-lessThanEqualsByteString-03 : Untyped
test-lessThanEqualsByteString-03 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "TheCakeIsALie")))) (UCon (tagCon bytestring (mkByteString "TheCakeIsALie"))))

expected-lessThanEqualsByteString-03 : Result
expected-lessThanEqualsByteString-03 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `lessThanEqualsByteString`.
pending-lessThanEqualsByteString-03 : Set
pending-lessThanEqualsByteString-03 = Pending (evalRaw test-lessThanEqualsByteString-03 ≡ expected-lessThanEqualsByteString-03)
```
