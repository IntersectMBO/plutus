---
title: Conformance.Builtin.Parser.Bytestring
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/parser/bytestring`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Parser.Bytestring where

open import Conformance.Eval
```

## bytestring-01

```
-- builtin/parser/bytestring/bytestring-01
test-bytestring-01 : Untyped
test-bytestring-01 = (UCon (tagCon bytestring (mkByteString "\NUL\255")))

expected-bytestring-01 : Result
expected-bytestring-01 = success (UCon (tagCon bytestring (mkByteString "\NUL\255")))

-- Pending: bytestring constant.
pending-bytestring-01 : Set
pending-bytestring-01 = Pending (evalRaw test-bytestring-01 ≡ expected-bytestring-01)
```

## bytestring-02

```
-- builtin/parser/bytestring/bytestring-02
test-bytestring-02 : Untyped
test-bytestring-02 = (UCon (tagCon bytestring (mkByteString "TheCakeIsALie")))

expected-bytestring-02 : Result
expected-bytestring-02 = success (UCon (tagCon bytestring (mkByteString "TheCakeIsALie")))

-- Pending: bytestring constant.
pending-bytestring-02 : Set
pending-bytestring-02 = Pending (evalRaw test-bytestring-02 ≡ expected-bytestring-02)
```

## bytestring-03

```
-- builtin/parser/bytestring/bytestring-03
test-bytestring-03 : Untyped
test-bytestring-03 = (UCon (tagCon bytestring (mkByteString "")))

expected-bytestring-03 : Result
expected-bytestring-03 = success (UCon (tagCon bytestring (mkByteString "")))

-- Pending: bytestring constant.
pending-bytestring-03 : Set
pending-bytestring-03 = Pending (evalRaw test-bytestring-03 ≡ expected-bytestring-03)
```

## bytestring-04

Skipped: the program does not parse (`parse/decode error`).
