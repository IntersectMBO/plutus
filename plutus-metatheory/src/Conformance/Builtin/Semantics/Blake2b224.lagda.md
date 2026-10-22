---
title: Conformance.Builtin.Semantics.Blake2b224
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/blake2b_224`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Blake2b224 where

open import Conformance.Eval
```

## blake2b_224-empty

```
-- builtin/semantics/blake2b_224/blake2b_224-empty
-- Test vector (0-bit input) for Blake2b_224.
-- Output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
test-blake2b-224-empty : Untyped
test-blake2b-224-empty = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-224) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "836cc68931c2e4e3e838602eca1902591d216837bafddfe6f0c8cb07"))))

expected-blake2b-224-empty : Result
expected-blake2b-224-empty = success (UCon (tagCon bool true))

-- Pending: postulated builtin `blake2b-224`.
pending-blake2b-224-empty : Set
pending-blake2b-224-empty = Pending (evalRaw test-blake2b-224-empty ≡ expected-blake2b-224-empty)
```

## blake2b_224-length-200

```
-- builtin/semantics/blake2b_224/blake2b_224-length-200
-- Test vector (200-bit input) for Blake2b_224.
-- Output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
test-blake2b-224-length-200 : Untyped
test-blake2b-224-length-200 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-224) (UCon (tagCon bytestring (mkByteString "2e7ea84da4bc4d7cfb463e3f2c8647057afff3fbececa1d200"))))) (UCon (tagCon bytestring (mkByteString "93d4b80c531998973b08297fc5042af359865a8702f20b5fc2db8df5"))))

expected-blake2b-224-length-200 : Result
expected-blake2b-224-length-200 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `blake2b-224`.
pending-blake2b-224-length-200 : Set
pending-blake2b-224-length-200 = Pending (evalRaw test-blake2b-224-length-200 ≡ expected-blake2b-224-length-200)
```
