---
title: Conformance.Builtin.Semantics.Bls12381G1HashToGroup
layout: page
---

<!-- GENERATED FILE: do not edit.
<<<<<<< HEAD
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
=======
     Regenerate with `generate-agda-typecheck-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-typecheck-conformance` from the
>>>>>>> origin/master
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
<<<<<<< HEAD
test-hash = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "0a")))))

expected-hash : Result
expected-hash = success (UCon (tagCon bytestring (mkByteString "a45ddef02cdd86039be4b0a863cba70ea903194ea0489ce619c6276175839d62eea72b095d6566067f4a44b85614f199")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-hashToGroup`.
=======
test-hash = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "\142")))) (UCon (tagCon bytestring (mkByteString "\n")))))

expected-hash : Result
expected-hash = success (UCon (tagCon bytestring (mkByteString "\164]\222\240,\221\134\ETX\155\228\176\168c\203\167\SO\169\ETX\EMN\160H\156\230\EM\198'au\131\157b\238\167+\t]ef\ACK\DELJD\184V\DC4\241\153")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-hashToGroup`.
>>>>>>> origin/master
pending-hash : Set
pending-hash = Pending (evalRaw test-hash ≡ expected-hash)
```

## hash-different-msg-same-dst

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash-different-msg-same-dst
-- Check that hashing different messages with the same DST gives different
-- results: this should return False.
test-hash-different-msg-same-dst : Untyped
<<<<<<< HEAD
test-hash-different-msg-same-dst = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "0a"))))) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "81")))) (UCon (tagCon bytestring (mkByteString "0a")))))
=======
test-hash-different-msg-same-dst = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "\142")))) (UCon (tagCon bytestring (mkByteString "\n"))))) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "\129")))) (UCon (tagCon bytestring (mkByteString "\n")))))
>>>>>>> origin/master

expected-hash-different-msg-same-dst : Result
expected-hash-different-msg-same-dst = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-hashToGroup`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-hashToGroup`.
>>>>>>> origin/master
pending-hash-different-msg-same-dst : Set
pending-hash-different-msg-same-dst = Pending (evalRaw test-hash-different-msg-same-dst ≡ expected-hash-different-msg-same-dst)
```

## hash-dst-len-255

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash-dst-len-255
-- Maximum length of DST is 255 bytes: this should be OK
test-hash-dst-len-255 : Untyped
<<<<<<< HEAD
test-hash-dst-len-255 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "3f")))) (UCon (tagCon bytestring (mkByteString "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890")))))

expected-hash-dst-len-255 : Result
expected-hash-dst-len-255 = success (UCon (tagCon bytestring (mkByteString "931bd1f65dd2d34a55c93d82c20dcacd3a91afa5932fdd7fed06119f8574520c9609d337d680060b4bd2c59f0b60bb54")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-hashToGroup`.
=======
test-hash-dst-len-255 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "?")))) (UCon (tagCon bytestring (mkByteString "\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144")))))

expected-hash-dst-len-255 : Result
expected-hash-dst-len-255 = success (UCon (tagCon bytestring (mkByteString "\147\ESC\209\246]\210\211JU\201=\130\194\r\202\205:\145\175\165\147/\221\DEL\237\ACK\DC1\159\133tR\f\150\t\211\&7\214\128\ACK\vK\210\197\159\v`\187T")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-hashToGroup`.
>>>>>>> origin/master
pending-hash-dst-len-255 : Set
pending-hash-dst-len-255 = Pending (evalRaw test-hash-dst-len-255 ≡ expected-hash-dst-len-255)
```

## hash-dst-len-256

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash-dst-len-256
-- Maximum length of DST is 255 bytes: this should fail
test-hash-dst-len-256 : Untyped
<<<<<<< HEAD
test-hash-dst-len-256 = (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "3f")))) (UCon (tagCon bytestring (mkByteString "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890ff"))))
=======
test-hash-dst-len-256 = (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "?")))) (UCon (tagCon bytestring (mkByteString "\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\255"))))
>>>>>>> origin/master

expected-hash-dst-len-256 : Result
expected-hash-dst-len-256 = failure

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-hashToGroup`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-hashToGroup`.
>>>>>>> origin/master
pending-hash-dst-len-256 : Set
pending-hash-dst-len-256 = Pending (evalRaw test-hash-dst-len-256 ≡ expected-hash-dst-len-256)
```

## hash-empty-dst

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash-empty-dst
-- Check that hashing a random bytestring with an empty DST gives the expected result.
test-hash-empty-dst : Untyped
<<<<<<< HEAD
test-hash-empty-dst = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "")))))

expected-hash-empty-dst : Result
expected-hash-empty-dst = success (UCon (tagCon bytestring (mkByteString "9019067bf1fa5b2a7a40fb31a70c66f25a3de7e3ef42f8365c9b7963dc01e15a2e086df6d1a181b1d12811a520440909")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-hashToGroup`.
=======
test-hash-empty-dst = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "\142")))) (UCon (tagCon bytestring (mkByteString "")))))

expected-hash-empty-dst : Result
expected-hash-empty-dst = success (UCon (tagCon bytestring (mkByteString "\144\EM\ACK{\241\250[*z@\251\&1\167\ff\242Z=\231\227\239B\248\&6\\\155yc\220\SOH\225Z.\bm\246\209\161\129\177\209(\DC1\165 D\t\t")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-hashToGroup`.
>>>>>>> origin/master
pending-hash-empty-dst : Set
pending-hash-empty-dst = Pending (evalRaw test-hash-empty-dst ≡ expected-hash-empty-dst)
```

## hash-same-msg-different-dst

```
-- builtin/semantics/bls12_381_G1_hashToGroup/hash-same-msg-different-dst
-- Check that hashing the same message with different DSTs gives different
-- results: this should return False.
test-hash-same-msg-different-dst : Untyped
<<<<<<< HEAD
test-hash-same-msg-different-dst = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "0a"))))) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "8e")))) (UCon (tagCon bytestring (mkByteString "01")))))
=======
test-hash-same-msg-different-dst = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "\142")))) (UCon (tagCon bytestring (mkByteString "\n"))))) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "\142")))) (UCon (tagCon bytestring (mkByteString "\SOH")))))
>>>>>>> origin/master

expected-hash-same-msg-different-dst : Result
expected-hash-same-msg-different-dst = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-hashToGroup`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-hashToGroup`.
>>>>>>> origin/master
pending-hash-same-msg-different-dst : Set
pending-hash-same-msg-different-dst = Pending (evalRaw test-hash-same-msg-different-dst ≡ expected-hash-same-msg-different-dst)
```
