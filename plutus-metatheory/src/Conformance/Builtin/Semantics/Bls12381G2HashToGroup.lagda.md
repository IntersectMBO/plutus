---
title: Conformance.Builtin.Semantics.Bls12381G2HashToGroup
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

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
test-hash = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "\142")))) (UCon (tagCon bytestring (mkByteString "\n")))))

expected-hash : Result
expected-hash = success (UCon (tagCon bytestring (mkByteString "\171\219\ACKM\186\169\134\217`\151\150\215\168\SO\240\DELq\159\153\250]\152v\224\US\146\152y=L~{\169\178\197]\166\137o\144i:\215j\t=(\SOH\CAN\164\194M\249\163\135\234\248[\NAK\146se\161\DLE\254RV\245=\223\139\239@i\254v\GS\130\NAK\212\167>\201\128\241\168\SOH\219\171\162QF\182\202~\a")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash : Set
pending-hash = Pending (evalRaw test-hash ≡ expected-hash)
```

## hash-different-msg-same-dst

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash-different-msg-same-dst
-- Check that hashing different messages with the same DST gives different
-- results: this should return False.
test-hash-different-msg-same-dst : Untyped
test-hash-different-msg-same-dst = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "\142")))) (UCon (tagCon bytestring (mkByteString "\n"))))) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "\129")))) (UCon (tagCon bytestring (mkByteString "\n")))))

expected-hash-different-msg-same-dst : Result
expected-hash-different-msg-same-dst = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash-different-msg-same-dst : Set
pending-hash-different-msg-same-dst = Pending (evalRaw test-hash-different-msg-same-dst ≡ expected-hash-different-msg-same-dst)
```

## hash-dst-len-255

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash-dst-len-255
-- Maximum length of DST is 255 bytes: this should be OK
test-hash-dst-len-255 : Untyped
test-hash-dst-len-255 = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "?")))) (UCon (tagCon bytestring (mkByteString "\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144")))))

expected-hash-dst-len-255 : Result
expected-hash-dst-len-255 = success (UCon (tagCon bytestring (mkByteString "\144(\181\aDKB\131\250\242\248^\DEL}8\144\182~\155\207\132\199\222/u\254`9\150\171\ESC\DC2\162[F7\214\143\&1\v{\214\212~\193\RS?\166\r\SI\143\157\GS\200\128ta\ENQ\180\215\233\181\187\168j\191\222\249m\253\163\ETX\177\251\NUL\181\216f\181\215\246x\131\239\179\158\252\163\SOH\174D\167\241\&2*3")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash-dst-len-255 : Set
pending-hash-dst-len-255 = Pending (evalRaw test-hash-dst-len-255 ≡ expected-hash-dst-len-255)
```

## hash-dst-len-256

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash-dst-len-256
-- Maximum length of DST is 255 bytes: this should fail
test-hash-dst-len-256 : Untyped
test-hash-dst-len-256 = (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "?")))) (UCon (tagCon bytestring (mkByteString "\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\DC24Vx\144\255"))))

expected-hash-dst-len-256 : Result
expected-hash-dst-len-256 = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash-dst-len-256 : Set
pending-hash-dst-len-256 = Pending (evalRaw test-hash-dst-len-256 ≡ expected-hash-dst-len-256)
```

## hash-empty-dst

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash-empty-dst
-- Check that hashing a random bytestring with an empty DST gives the expected result.
test-hash-empty-dst : Untyped
test-hash-empty-dst = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "\142")))) (UCon (tagCon bytestring (mkByteString "")))))

expected-hash-empty-dst : Result
expected-hash-empty-dst = success (UCon (tagCon bytestring (mkByteString "\135\133\&3K\188\207\159z\ESC\198V\252\188\175\153\SOHR\FS\192\154\ao\246\157@\228g\b+`]f\130\EMt}\254\195|y\140\151\178\199\242\142\201\SOH\ETB\196\204\252T\239<\195\192\ETX\137Q\196\150\154<\v?\184B\167\129\ETXXfWB\138\179\141q\156\157\&3\DC4\222Vl\217U@\170\204\247\175\212\136!")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash-empty-dst : Set
pending-hash-empty-dst = Pending (evalRaw test-hash-empty-dst ≡ expected-hash-empty-dst)
```

## hash-same-msg-different-dst

```
-- builtin/semantics/bls12_381_G2_hashToGroup/hash-same-msg-different-dst
-- Check that hashing the same message with different DSTs gives different
-- results: this should return False.
test-hash-same-msg-different-dst : Untyped
test-hash-same-msg-different-dst = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "\142")))) (UCon (tagCon bytestring (mkByteString "\n"))))) (UApp (UApp (UBuiltin bls12-381-G2-hashToGroup) (UCon (tagCon bytestring (mkByteString "\142")))) (UCon (tagCon bytestring (mkByteString "\SOH")))))

expected-hash-same-msg-different-dst : Result
expected-hash-same-msg-different-dst = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-hashToGroup`.
pending-hash-same-msg-different-dst : Set
pending-hash-same-msg-different-dst = Pending (evalRaw test-hash-same-msg-different-dst ≡ expected-hash-same-msg-different-dst)
```
