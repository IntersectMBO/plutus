---
title: Conformance.Builtin.Semantics.Bls12381G1Uncompress
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
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G1_uncompress`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G1Uncompress where

open import Conformance.Eval
```

## bad-zero-01

```
-- builtin/semantics/bls12_381_G1_uncompress/bad-zero-01
-- This has the infinity bit set but not the compression bit, and so is invalid.
test-bad-zero-01 : Untyped
<<<<<<< HEAD
test-bad-zero-01 = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))
=======
test-bad-zero-01 = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "@\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))
>>>>>>> origin/master

expected-bad-zero-01 : Result
expected-bad-zero-01 = failure

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-bad-zero-01 : Set
pending-bad-zero-01 = Pending (evalRaw test-bad-zero-01 ≡ expected-bad-zero-01)
```

## bad-zero-02

```
-- builtin/semantics/bls12_381_G1_uncompress/bad-zero-02
-- This is the zero point of G1, but with the sign bit set.  It should fail to uncompress.
test-bad-zero-02 : Untyped
<<<<<<< HEAD
test-bad-zero-02 = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))
=======
test-bad-zero-02 = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\224\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))
>>>>>>> origin/master

expected-bad-zero-02 : Result
expected-bad-zero-02 = failure

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-bad-zero-02 : Set
pending-bad-zero-02 = Pending (evalRaw test-bad-zero-02 ≡ expected-bad-zero-02)
```

## bad-zero-03

```
-- builtin/semantics/bls12_381_G1_uncompress/bad-zero-03
-- This is the zero point of G1, but with a random bit set in the body.  It
-- should fail to uncompress.
test-bad-zero-03 : Untyped
<<<<<<< HEAD
test-bad-zero-03 = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000"))))
=======
test-bad-zero-03 = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\DLE\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))
>>>>>>> origin/master

expected-bad-zero-03 : Result
expected-bad-zero-03 = failure

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-bad-zero-03 : Set
pending-bad-zero-03 = Pending (evalRaw test-bad-zero-03 ≡ expected-bad-zero-03)
```

## off-curve

```
-- builtin/semantics/bls12_381_G1_uncompress/off-curve
-- This contains a value which is not the x-coordinate of a point on the E1 curve.
test-off-curve : Untyped
<<<<<<< HEAD
test-off-curve = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003"))))
=======
test-off-curve = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\160\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\ETX"))))
>>>>>>> origin/master

expected-off-curve : Result
expected-off-curve = failure

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-off-curve : Set
pending-off-curve = Pending (evalRaw test-off-curve ≡ expected-off-curve)
```

## on-curve-bit1-clear

```
-- builtin/semantics/bls12_381_G1_uncompress/on-curve-bit1-clear
-- This value was obtained by hashing 0x0102030405 to G1 but has had the
-- compression bit cleared, so uncompression should fail.
test-on-curve-bit1-clear : Untyped
<<<<<<< HEAD
test-on-curve-bit1-clear = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "21e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb"))))
=======
test-on-curve-bit1-clear = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "!\233\160\198\137\133\ENQ\155\210Z^\240[5\FS\162/}|\EM\227y(X:\225*\USI9D\SI\247T\207\216[#\223JT\246lp\137\219m\235"))))
>>>>>>> origin/master

expected-on-curve-bit1-clear : Result
expected-on-curve-bit1-clear = failure

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-on-curve-bit1-clear : Set
pending-on-curve-bit1-clear = Pending (evalRaw test-on-curve-bit1-clear ≡ expected-on-curve-bit1-clear)
```

## on-curve-bit3-clear

```
-- builtin/semantics/bls12_381_G1_uncompress/on-curve-bit3-clear
-- This value was obtained by hashing 0x0102030405 to G1.  The sign bit was set
-- but has been cleared: this negates the point, so uncompression should still
-- succeed.
test-on-curve-bit3-clear : Untyped
<<<<<<< HEAD
test-on-curve-bit3-clear = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "81e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb")))))

expected-on-curve-bit3-clear : Result
expected-on-curve-bit3-clear = success (UCon (tagCon bytestring (mkByteString "81e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-uncompress`.
=======
test-on-curve-bit3-clear = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\129\233\160\198\137\133\ENQ\155\210Z^\240[5\FS\162/}|\EM\227y(X:\225*\USI9D\SI\247T\207\216[#\223JT\246lp\137\219m\235")))))

expected-on-curve-bit3-clear : Result
expected-on-curve-bit3-clear = success (UCon (tagCon bytestring (mkByteString "\129\233\160\198\137\133\ENQ\155\210Z^\240[5\FS\162/}|\EM\227y(X:\225*\USI9D\SI\247T\207\216[#\223JT\246lp\137\219m\235")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-on-curve-bit3-clear : Set
pending-on-curve-bit3-clear = Pending (evalRaw test-on-curve-bit3-clear ≡ expected-on-curve-bit3-clear)
```

## on-curve-bit3-set

```
-- builtin/semantics/bls12_381_G1_uncompress/on-curve-bit3-set
-- This value was obtained by hashing 0x0102030405 to G1.  No changes have been
-- made, so uncompression should succeed.
test-on-curve-bit3-set : Untyped
<<<<<<< HEAD
test-on-curve-bit3-set = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "a1e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb")))))

expected-on-curve-bit3-set : Result
expected-on-curve-bit3-set = success (UCon (tagCon bytestring (mkByteString "a1e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-uncompress`.
=======
test-on-curve-bit3-set = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\161\233\160\198\137\133\ENQ\155\210Z^\240[5\FS\162/}|\EM\227y(X:\225*\USI9D\SI\247T\207\216[#\223JT\246lp\137\219m\235")))))

expected-on-curve-bit3-set : Result
expected-on-curve-bit3-set = success (UCon (tagCon bytestring (mkByteString "\161\233\160\198\137\133\ENQ\155\210Z^\240[5\FS\162/}|\EM\227y(X:\225*\USI9D\SI\247T\207\216[#\223JT\246lp\137\219m\235")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-on-curve-bit3-set : Set
pending-on-curve-bit3-set = Pending (evalRaw test-on-curve-bit3-set ≡ expected-on-curve-bit3-set)
```

## on-curve-serialised-not-compressed

```
-- builtin/semantics/bls12_381_G1_uncompress/on-curve-serialised-not-compressed
-- This checks that the uncompression function fails on a valid *serialised* G1
-- point (obtained by hashing 0x0102030405 onto G1).  The deserialisation
-- function in the blst library can handle both serialised and compressed
-- points, but we should fail on the former.
test-on-curve-serialised-not-compressed : Untyped
<<<<<<< HEAD
test-on-curve-serialised-not-compressed = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "01e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb12ae8470d881eb628dfcf4bb083fb8a6968d907a0c265f6d06e04b05a19418d395d3e0c115430f88e7156822904ef5bf"))))
=======
test-on-curve-serialised-not-compressed = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\SOH\233\160\198\137\133\ENQ\155\210Z^\240[5\FS\162/}|\EM\227y(X:\225*\USI9D\SI\247T\207\216[#\223JT\246lp\137\219m\235\DC2\174\132p\216\129\235b\141\252\244\187\b?\184\166\150\141\144z\f&_m\ACK\224K\ENQ\161\148\CAN\211\149\211\224\193\NAKC\SI\136\231\NAKh\"\144N\245\191"))))
>>>>>>> origin/master

expected-on-curve-serialised-not-compressed : Result
expected-on-curve-serialised-not-compressed = failure

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-on-curve-serialised-not-compressed : Set
pending-on-curve-serialised-not-compressed = Pending (evalRaw test-on-curve-serialised-not-compressed ≡ expected-on-curve-serialised-not-compressed)
```

## out-of-group

```
-- builtin/semantics/bls12_381_G1_uncompress/out-of-group
-- This contains a value which is the x-coordinate of a point which lies on the
-- E1 curve but not the G1 subgroup.
test-out-of-group : Untyped
<<<<<<< HEAD
test-out-of-group = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005"))))
=======
test-out-of-group = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\160\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\ENQ"))))
>>>>>>> origin/master

expected-out-of-group : Result
expected-out-of-group = failure

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-out-of-group : Set
pending-out-of-group = Pending (evalRaw test-out-of-group ≡ expected-out-of-group)
```

## too-long

```
-- builtin/semantics/bls12_381_G1_uncompress/too-long
-- The bytestring is the compressed version of the G1 zero point, but extended
-- to 49 bytes.
test-too-long : Untyped
<<<<<<< HEAD
test-too-long = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))
=======
test-too-long = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))
>>>>>>> origin/master

expected-too-long : Result
expected-too-long = failure

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-too-long : Set
pending-too-long = Pending (evalRaw test-too-long ≡ expected-too-long)
```

## too-short

```
-- builtin/semantics/bls12_381_G1_uncompress/too-short
-- The bytestring is the compressed version of the G1 zero point, but truncated to 47 bytes.
test-too-short : Untyped
<<<<<<< HEAD
test-too-short = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))
=======
test-too-short = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))
>>>>>>> origin/master

expected-too-short : Result
expected-too-short = failure

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-too-short : Set
pending-too-short = Pending (evalRaw test-too-short ≡ expected-too-short)
```

## zero

```
-- builtin/semantics/bls12_381_G1_uncompress/zero
-- The zero element of G1 uncompresses correctly.
test-zero : Untyped
<<<<<<< HEAD
test-zero = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))))

expected-zero : Result
expected-zero = success (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-uncompress`.
=======
test-zero = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))))

expected-zero : Result
expected-zero = success (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-zero : Set
pending-zero = Pending (evalRaw test-zero ≡ expected-zero)
```
