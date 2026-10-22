---
title: Conformance.Builtin.Semantics.Bls12381G1HashToGroup
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G1_hashToGroup`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G1HashToGroup where

open import Conformance.Eval
```

## hash

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash
-- Check that hashing a random bytestring gives the expected result.
test-hash : Untyped
test-hash = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "0a")))))

expected-hash : Result
expected-hash = success (UCon (tagCon bytestring (mkByteString "a45ddef02cdd86039be4b0a863cba70ea903194ea0489ce619c6276175839d62eea72b095d6566067f4a44b85614f199")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-hashToGroup`.
pending-hash : Set
pending-hash = Pending (evalRaw test-hash ≡ expected-hash)
```

## hash-different-msg-same-dst

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash-different-msg-same-dst
-- Check that hashing different messages with the same DST gives different
-- results: this should return False.
test-hash-different-msg-same-dst : Untyped
test-hash-different-msg-same-dst = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "0a"))))) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "81")))) (UCon (tagCon bytestring (mkByteString "0a")))))

expected-hash-different-msg-same-dst : Result
expected-hash-different-msg-same-dst = success (UCon (tagCon bool false))

-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-hashToGroup`.
pending-hash-different-msg-same-dst : Set
pending-hash-different-msg-same-dst = Pending (evalRaw test-hash-different-msg-same-dst ≡ expected-hash-different-msg-same-dst)
```

## hash-dst-len-255

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash-dst-len-255
-- Maximum length of DST is 255 bytes: this should be OK
test-hash-dst-len-255 : Untyped
test-hash-dst-len-255 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "3f")))) (UCon (tagCon bytestring (mkByteString "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890")))))

expected-hash-dst-len-255 : Result
expected-hash-dst-len-255 = success (UCon (tagCon bytestring (mkByteString "931bd1f65dd2d34a55c93d82c20dcacd3a91afa5932fdd7fed06119f8574520c9609d337d680060b4bd2c59f0b60bb54")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-hashToGroup`.
pending-hash-dst-len-255 : Set
pending-hash-dst-len-255 = Pending (evalRaw test-hash-dst-len-255 ≡ expected-hash-dst-len-255)
```

## hash-dst-len-256

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash-dst-len-256
-- Maximum length of DST is 255 bytes: this should fail
test-hash-dst-len-256 : Untyped
test-hash-dst-len-256 = (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "3f")))) (UCon (tagCon bytestring (mkByteString "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890ff"))))

expected-hash-dst-len-256 : Result
expected-hash-dst-len-256 = failure

-- Pending: postulated builtin `bls12-381-G1-hashToGroup`.
pending-hash-dst-len-256 : Set
pending-hash-dst-len-256 = Pending (evalRaw test-hash-dst-len-256 ≡ expected-hash-dst-len-256)
```

## hash-empty-dst

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash-empty-dst
-- Check that hashing a random bytestring with an empty DST gives the expected result.
test-hash-empty-dst : Untyped
test-hash-empty-dst = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "")))))

expected-hash-empty-dst : Result
expected-hash-empty-dst = success (UCon (tagCon bytestring (mkByteString "9019067bf1fa5b2a7a40fb31a70c66f25a3de7e3ef42f8365c9b7963dc01e15a2e086df6d1a181b1d12811a520440909")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-hashToGroup`.
pending-hash-empty-dst : Set
pending-hash-empty-dst = Pending (evalRaw test-hash-empty-dst ≡ expected-hash-empty-dst)
```

## hash-same-msg-different-dst

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash-same-msg-different-dst
-- Check that hashing the same message with different DSTs gives different
-- results: this should return False.
test-hash-same-msg-different-dst : Untyped
test-hash-same-msg-different-dst = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "0a"))))) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "01")))))

expected-hash-same-msg-different-dst : Result
expected-hash-same-msg-different-dst = success (UCon (tagCon bool false))

-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-hashToGroup`.
pending-hash-same-msg-different-dst : Set
pending-hash-same-msg-different-dst = Pending (evalRaw test-hash-same-msg-different-dst ≡ expected-hash-same-msg-different-dst)
```
