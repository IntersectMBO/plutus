---
title: Conformance.Builtin.Semantics.Bls12381G2Uncompress
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G2_uncompress`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G2Uncompress where

open import Conformance.Eval
```

## bad-zero-01

```
-- builtin/semantics/bls12_381_G2_uncompress/bad-zero-01
-- This has the infinity bit set but not the compression bit, and so is invalid.
test-bad-zero-01 : Untyped
test-bad-zero-01 = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))

expected-bad-zero-01 : Result
expected-bad-zero-01 = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-bad-zero-01 : Set
pending-bad-zero-01 = Pending (evalRaw test-bad-zero-01 ≡ expected-bad-zero-01)
```

## bad-zero-02

```
-- builtin/semantics/bls12_381_G2_uncompress/bad-zero-02
-- This is the zero point of G2, but with the sign bit set.  It should fail to uncompress.
test-bad-zero-02 : Untyped
test-bad-zero-02 = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))

expected-bad-zero-02 : Result
expected-bad-zero-02 = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-bad-zero-02 : Set
pending-bad-zero-02 = Pending (evalRaw test-bad-zero-02 ≡ expected-bad-zero-02)
```

## bad-zero-03

```
-- builtin/semantics/bls12_381_G2_uncompress/bad-zero-03
-- This is the zero point of G2, but with the sign bit set.  It should fail to
-- uncompress.
test-bad-zero-03 : Untyped
test-bad-zero-03 = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000"))))

expected-bad-zero-03 : Result
expected-bad-zero-03 = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-bad-zero-03 : Set
pending-bad-zero-03 = Pending (evalRaw test-bad-zero-03 ≡ expected-bad-zero-03)
```

## off-curve

```
-- builtin/semantics/bls12_381_G2_uncompress/off-curve
-- This contains a value which is not the x-coordinate of a point on the E2 curve.
test-off-curve : Untyped
test-off-curve = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003"))))

expected-off-curve : Result
expected-off-curve = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-off-curve : Set
pending-off-curve = Pending (evalRaw test-off-curve ≡ expected-off-curve)
```

## on-curve-bit1-clear

```
-- builtin/semantics/bls12_381_G2_uncompress/on-curve-bit1-clear
-- This value was obtained by hashing 0x0102030405 to G2 but has had the
-- compression bit cleared, so uncompression should fail.
test-on-curve-bit1-clear : Untyped
test-on-curve-bit1-clear = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "28138ebea766d4d1aa64dd3b5826244c32ea3fe9351f9c8d584203716dae151d14bb5d06e245c24877955c79287682ba082d077bbb2afdb1ad1d48d18e2f0c56b001bce207801adfa9fd451fc59d56f0433b02f921ba5a272c58c06536291d07"))))

expected-on-curve-bit1-clear : Result
expected-on-curve-bit1-clear = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-on-curve-bit1-clear : Set
pending-on-curve-bit1-clear = Pending (evalRaw test-on-curve-bit1-clear ≡ expected-on-curve-bit1-clear)
```

## on-curve-bit3-clear

```
-- builtin/semantics/bls12_381_G2_uncompress/on-curve-bit3-clear
-- This value was obtained by hashing 0x0102030405 to G2.  The sign bit was set
-- but has been cleared: this negates the point, so uncompression should still
-- succeed.
test-on-curve-bit3-clear : Untyped
test-on-curve-bit3-clear = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "88138ebea766d4d1aa64dd3b5826244c32ea3fe9351f9c8d584203716dae151d14bb5d06e245c24877955c79287682ba082d077bbb2afdb1ad1d48d18e2f0c56b001bce207801adfa9fd451fc59d56f0433b02f921ba5a272c58c06536291d07")))))

expected-on-curve-bit3-clear : Result
expected-on-curve-bit3-clear = success (UCon (tagCon bytestring (mkByteString "88138ebea766d4d1aa64dd3b5826244c32ea3fe9351f9c8d584203716dae151d14bb5d06e245c24877955c79287682ba082d077bbb2afdb1ad1d48d18e2f0c56b001bce207801adfa9fd451fc59d56f0433b02f921ba5a272c58c06536291d07")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-uncompress`.
pending-on-curve-bit3-clear : Set
pending-on-curve-bit3-clear = Pending (evalRaw test-on-curve-bit3-clear ≡ expected-on-curve-bit3-clear)
```

## on-curve-bit3-set

```
-- builtin/semantics/bls12_381_G2_uncompress/on-curve-bit3-set
-- This value was obtained by hashing 0x0102030405 to G2.  No changes have been
-- made, so uncompression should succeed.
test-on-curve-bit3-set : Untyped
test-on-curve-bit3-set = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a8138ebea766d4d1aa64dd3b5826244c32ea3fe9351f9c8d584203716dae151d14bb5d06e245c24877955c79287682ba082d077bbb2afdb1ad1d48d18e2f0c56b001bce207801adfa9fd451fc59d56f0433b02f921ba5a272c58c06536291d07")))))

expected-on-curve-bit3-set : Result
expected-on-curve-bit3-set = success (UCon (tagCon bytestring (mkByteString "a8138ebea766d4d1aa64dd3b5826244c32ea3fe9351f9c8d584203716dae151d14bb5d06e245c24877955c79287682ba082d077bbb2afdb1ad1d48d18e2f0c56b001bce207801adfa9fd451fc59d56f0433b02f921ba5a272c58c06536291d07")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-uncompress`.
pending-on-curve-bit3-set : Set
pending-on-curve-bit3-set = Pending (evalRaw test-on-curve-bit3-set ≡ expected-on-curve-bit3-set)
```

## on-curve-serialised-not-compressed

```
-- builtin/semantics/bls12_381_G2_uncompress/on-curve-serialised-not-compressed
-- This checks that the uncompression function fails on a valid *serialised* G2
-- point (obtained by hashing 0x0102030405 onto G2).  The deserialisation
-- function in the blst library can handle both serialised and compressed
-- points, but we should fail on the former.
test-on-curve-serialised-not-compressed : Untyped
test-on-curve-serialised-not-compressed = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "08138ebea766d4d1aa64dd3b5826244c32ea3fe9351f9c8d584203716dae151d14bb5d06e245c24877955c79287682ba082d077bbb2afdb1ad1d48d18e2f0c56b001bce207801adfa9fd451fc59d56f0433b02f921ba5a272c58c06536291d071676b275e27060b26dd91aac0a1feb56d1c1de7c323f486e48d54eae0c3c8f4caa45faad589c5d180ac0830dcdb3ecd8126c9c5db86cdf7129cf18582013d267a7c2827a901ef61ab58e7ef150219441abc57671eb39009f6bb166bcbade700d"))))

expected-on-curve-serialised-not-compressed : Result
expected-on-curve-serialised-not-compressed = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-on-curve-serialised-not-compressed : Set
pending-on-curve-serialised-not-compressed = Pending (evalRaw test-on-curve-serialised-not-compressed ≡ expected-on-curve-serialised-not-compressed)
```

## out-of-group

```
-- builtin/semantics/bls12_381_G2_uncompress/out-of-group
-- This contains a value which is the x-coordinate of a point which lies on the
-- E2 curve but not the G2 subgroup.
test-out-of-group : Untyped
test-out-of-group = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005"))))

expected-out-of-group : Result
expected-out-of-group = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-out-of-group : Set
pending-out-of-group = Pending (evalRaw test-out-of-group ≡ expected-out-of-group)
```

## too-long

```
-- builtin/semantics/bls12_381_G2_uncompress/too-long
-- The bytestring is the compressed version of the G2 zero point, but extended to 97 bytes.
test-too-long : Untyped
test-too-long = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))

expected-too-long : Result
expected-too-long = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-too-long : Set
pending-too-long = Pending (evalRaw test-too-long ≡ expected-too-long)
```

## too-short

```
-- builtin/semantics/bls12_381_G2_uncompress/too-short
-- The bytestring is the compressed version of the G2 zero point, but truncated to 94 bytes.
test-too-short : Untyped
test-too-short = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))

expected-too-short : Result
expected-too-short = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-too-short : Set
pending-too-short = Pending (evalRaw test-too-short ≡ expected-too-short)
```

## zero

```
-- builtin/semantics/bls12_381_G2_uncompress/zero
-- The zero element of G2 uncompresses correctly.
test-zero : Untyped
test-zero = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))))

expected-zero : Result
expected-zero = success (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-uncompress`.
pending-zero : Set
pending-zero = Pending (evalRaw test-zero ≡ expected-zero)
```
