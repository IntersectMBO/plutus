---
title: Conformance.Builtin.Semantics.Blake2b256
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/blake2b_256`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Blake2b256 where

open import Conformance.Eval
```

## blake2b_256-empty

```
-- builtin/semantics/blake2b_256/blake2b_256-empty
-- Test vector (0-bit input) for Blake2b_256.
-- Output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
test-blake2b-256-empty : Untyped
test-blake2b-256-empty = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8"))))

expected-blake2b-256-empty : Result
expected-blake2b-256-empty = success (UCon (tagCon bool true))

-- Pending: postulated builtin `blake2b-256`.
pending-blake2b-256-empty : Set
pending-blake2b-256-empty = Pending (evalRaw test-blake2b-256-empty ≡ expected-blake2b-256-empty)
```

## blake2b_256-length-200

```
-- builtin/semantics/blake2b_256/blake2b_256-length-200
-- Test vector (200-bit input) for Blake2b_256.
-- Output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
test-blake2b-256-length-200 : Untyped
test-blake2b-256-length-200 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-256) (UCon (tagCon bytestring (mkByteString "2e7ea84da4bc4d7cfb463e3f2c8647057afff3fbececa1d200"))))) (UCon (tagCon bytestring (mkByteString "91c60f99b33303c02b39ed93b713e3915a180c3747f3b31e05727618ee401624"))))

expected-blake2b-256-length-200 : Result
expected-blake2b-256-length-200 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `blake2b-256`.
pending-blake2b-256-length-200 : Set
pending-blake2b-256-length-200 = Pending (evalRaw test-blake2b-256-length-200 ≡ expected-blake2b-256-length-200)
```
