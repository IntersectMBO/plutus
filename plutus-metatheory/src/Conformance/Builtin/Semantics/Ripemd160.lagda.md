---
title: Conformance.Builtin.Semantics.Ripemd160
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/ripemd_160`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Ripemd160 where

open import Conformance.Eval
```

## ripemd_160-empty

```
-- builtin/semantics/ripemd_160/ripemd_160-empty
-- Test vector (0-bit input) for Ripemd_160.
-- Output obtained using the online tool https://emn178.github.io/online-tools/ripemd_160.html
test-ripemd-160-empty : Untyped
test-ripemd-160-empty = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin ripemd-160) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "9c1185a5c5e9fc54612808977ee8f548b2258d31"))))

expected-ripemd-160-empty : Result
expected-ripemd-160-empty = success (UCon (tagCon bool true))

-- Pending: postulated builtin `ripemd-160`.
pending-ripemd-160-empty : Set
pending-ripemd-160-empty = Pending (evalRaw test-ripemd-160-empty ≡ expected-ripemd-160-empty)
```

## ripemd_160-length-200

```
-- builtin/semantics/ripemd_160/ripemd_160-length-200
-- Test vector (0-bit input) for Ripemd_160.
-- Output obtained using the online tool https://emn178.github.io/online-tools/ripemd_160.html
test-ripemd-160-length-200 : Untyped
test-ripemd-160-length-200 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin ripemd-160) (UCon (tagCon bytestring (mkByteString "2e7ea84da4bc4d7cfb463e3f2c8647057afff3fbececa1d200"))))) (UCon (tagCon bytestring (mkByteString "f18921115370b049e99dfdd49fc92b371dd7c7e9"))))

expected-ripemd-160-length-200 : Result
expected-ripemd-160-length-200 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `ripemd-160`.
pending-ripemd-160-length-200 : Set
pending-ripemd-160-length-200 = Pending (evalRaw test-ripemd-160-length-200 ≡ expected-ripemd-160-length-200)
```
