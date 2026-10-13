---
title: Conformance.Builtin.Semantics.Bls12381G2HashToGroup
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G2_hashToGroup`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G2HashToGroup where

open import Conformance.Eval
```

## hash

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash
-- Check that hashing a random bytestring gives the expected result.
test-hash : Untyped
test-hash = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "0a")))))

expected-hash : Result
expected-hash = success (UCon (tagCon bytestring (mkByteString "abdb064dbaa986d9609796d7a80ef07f719f99fa5d9876e01f9298793d4c7e7ba9b2c55da6896f90693ad76a093d280118a4c24df9a387eaf85b15927365a110fe5256f53ddf8bef4069fe761d8215d4a73ec980f1a801dbaba25146b6ca7e07")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash : Set
pending-hash = Pending (evalRaw test-hash ≡ expected-hash)
```

## hash-different-msg-same-dst

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash-different-msg-same-dst
-- Check that hashing different messages with the same DST gives different
-- results: this should return False.
test-hash-different-msg-same-dst : Untyped
test-hash-different-msg-same-dst = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "0a"))))) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "81")))) (UCon (tagCon bytestring (mkByteString "0a")))))

expected-hash-different-msg-same-dst : Result
expected-hash-different-msg-same-dst = success (UCon (tagCon bool false))

-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash-different-msg-same-dst : Set
pending-hash-different-msg-same-dst = Pending (evalRaw test-hash-different-msg-same-dst ≡ expected-hash-different-msg-same-dst)
```

## hash-dst-len-255

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash-dst-len-255
-- Maximum length of DST is 255 bytes: this should be OK
test-hash-dst-len-255 : Untyped
test-hash-dst-len-255 = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "3f")))) (UCon (tagCon bytestring (mkByteString "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890")))))

expected-hash-dst-len-255 : Result
expected-hash-dst-len-255 = success (UCon (tagCon bytestring (mkByteString "9028b507444b4283faf2f85e7f7d3890b67e9bcf84c7de2f75fe603996ab1b12a25b4637d68f310b7bd6d47ec11e3fa60d0f8f9d1dc880746105b4d7e9b5bba86abfdef96dfda303b1fb00b5d866b5d7f67883efb39efca301ae44a7f1322a33")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash-dst-len-255 : Set
pending-hash-dst-len-255 = Pending (evalRaw test-hash-dst-len-255 ≡ expected-hash-dst-len-255)
```

## hash-dst-len-256

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash-dst-len-256
-- Maximum length of DST is 255 bytes: this should fail
test-hash-dst-len-256 : Untyped
test-hash-dst-len-256 = (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "3f")))) (UCon (tagCon bytestring (mkByteString "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890ff"))))

expected-hash-dst-len-256 : Result
expected-hash-dst-len-256 = failure

-- Pending: postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash-dst-len-256 : Set
pending-hash-dst-len-256 = Pending (evalRaw test-hash-dst-len-256 ≡ expected-hash-dst-len-256)
```

## hash-empty-dst

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash-empty-dst
-- Check that hashing a random bytestring with an empty DST gives the expected result.
test-hash-empty-dst : Untyped
test-hash-empty-dst = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "")))))

expected-hash-empty-dst : Result
expected-hash-empty-dst = success (UCon (tagCon bytestring (mkByteString "8785334bbccf9f7a1bc656fcbcaf9901521cc09a076ff69d40e467082b605d668219747dfec37c798c97b2c7f28ec90117c4ccfc54ef3cc3c0038951c4969a3c0b3fb842a78103586657428ab38d719c9d3314de566cd95540aaccf7afd48821")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash-empty-dst : Set
pending-hash-empty-dst = Pending (evalRaw test-hash-empty-dst ≡ expected-hash-empty-dst)
```

## hash-same-msg-different-dst

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash-same-msg-different-dst
-- Check that hashing the same message with different DSTs gives different
-- results: this should return False.
test-hash-same-msg-different-dst : Untyped
test-hash-same-msg-different-dst = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "0a"))))) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "01")))))

expected-hash-same-msg-different-dst : Result
expected-hash-same-msg-different-dst = success (UCon (tagCon bool false))

-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash-same-msg-different-dst : Set
pending-hash-same-msg-different-dst = Pending (evalRaw test-hash-same-msg-different-dst ≡ expected-hash-same-msg-different-dst)
```
