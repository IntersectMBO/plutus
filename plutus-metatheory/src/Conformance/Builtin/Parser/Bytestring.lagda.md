---
title: Conformance.Builtin.Parser.Bytestring
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

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
test-bytestring-01 = (UCon (tagCon bytestring (mkByteString "00ff")))

expected-bytestring-01 : Result
expected-bytestring-01 = success (UCon (tagCon bytestring (mkByteString "00ff")))

_ : evalRaw test-bytestring-01 ≡ expected-bytestring-01
_ = refl
```

## bytestring-02

```
-- builtin/parser/bytestring/bytestring-02
test-bytestring-02 : Untyped
test-bytestring-02 = (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965")))

expected-bytestring-02 : Result
expected-bytestring-02 = success (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965")))

_ : evalRaw test-bytestring-02 ≡ expected-bytestring-02
_ = refl
```

## bytestring-03

```
-- builtin/parser/bytestring/bytestring-03
test-bytestring-03 : Untyped
test-bytestring-03 = (UCon (tagCon bytestring (mkByteString "")))

expected-bytestring-03 : Result
expected-bytestring-03 = success (UCon (tagCon bytestring (mkByteString "")))

_ : evalRaw test-bytestring-03 ≡ expected-bytestring-03
_ = refl
```

## bytestring-04

Skipped: the program does not parse or has free variables (`parse/decode error`).
