---
title: Conformance.Builtin.Semantics.Bls12381G2Uncompress
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

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
test-bad-zero-01 = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "@\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))

expected-bad-zero-01 : Result
expected-bad-zero-01 = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
pending-bad-zero-01 : Set
pending-bad-zero-01 = Pending (evalRaw test-bad-zero-01 ≡ expected-bad-zero-01)
```

## bad-zero-02

```
-- builtin/semantics/bls12_381_G2_uncompress/bad-zero-02
-- This is the zero point of G2, but with the sign bit set.  It should fail to uncompress.
test-bad-zero-02 : Untyped
test-bad-zero-02 = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\224\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))

expected-bad-zero-02 : Result
expected-bad-zero-02 = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
pending-bad-zero-02 : Set
pending-bad-zero-02 = Pending (evalRaw test-bad-zero-02 ≡ expected-bad-zero-02)
```

## bad-zero-03

```
-- builtin/semantics/bls12_381_G2_uncompress/bad-zero-03
-- This is the zero point of G2, but with the sign bit set.  It should fail to
-- uncompress.
test-bad-zero-03 : Untyped
test-bad-zero-03 = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\SOH\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))

expected-bad-zero-03 : Result
expected-bad-zero-03 = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
pending-bad-zero-03 : Set
pending-bad-zero-03 = Pending (evalRaw test-bad-zero-03 ≡ expected-bad-zero-03)
```

## off-curve

```
-- builtin/semantics/bls12_381_G2_uncompress/off-curve
-- This contains a value which is not the x-coordinate of a point on the E2 curve.
test-off-curve : Untyped
test-off-curve = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\160\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\ETX"))))

expected-off-curve : Result
expected-off-curve = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
pending-off-curve : Set
pending-off-curve = Pending (evalRaw test-off-curve ≡ expected-off-curve)
```

## on-curve-bit1-clear

```
-- builtin/semantics/bls12_381_G2_uncompress/on-curve-bit1-clear
-- This value was obtained by hashing 0x0102030405 to G2 but has had the
-- compression bit cleared, so uncompression should fail.
test-on-curve-bit1-clear : Untyped
test-on-curve-bit1-clear = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "(\DC3\142\190\167f\212\209\170d\221;X&$L2\234?\233\&5\US\156\141XB\ETXqm\174\NAK\GS\DC4\187]\ACK\226E\194Hw\149\\y(v\130\186\b-\a{\187*\253\177\173\GSH\209\142/\fV\176\SOH\188\226\a\128\SUB\223\169\253E\US\197\157V\240C;\STX\249!\186Z',X\192e6)\GS\a"))))

expected-on-curve-bit1-clear : Result
expected-on-curve-bit1-clear = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
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
test-on-curve-bit3-clear = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\136\DC3\142\190\167f\212\209\170d\221;X&$L2\234?\233\&5\US\156\141XB\ETXqm\174\NAK\GS\DC4\187]\ACK\226E\194Hw\149\\y(v\130\186\b-\a{\187*\253\177\173\GSH\209\142/\fV\176\SOH\188\226\a\128\SUB\223\169\253E\US\197\157V\240C;\STX\249!\186Z',X\192e6)\GS\a")))))

expected-on-curve-bit3-clear : Result
expected-on-curve-bit3-clear = success (UCon (tagCon bytestring (mkByteString "\136\DC3\142\190\167f\212\209\170d\221;X&$L2\234?\233\&5\US\156\141XB\ETXqm\174\NAK\GS\DC4\187]\ACK\226E\194Hw\149\\y(v\130\186\b-\a{\187*\253\177\173\GSH\209\142/\fV\176\SOH\188\226\a\128\SUB\223\169\253E\US\197\157V\240C;\STX\249!\186Z',X\192e6)\GS\a")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-uncompress`.
pending-on-curve-bit3-clear : Set
pending-on-curve-bit3-clear = Pending (evalRaw test-on-curve-bit3-clear ≡ expected-on-curve-bit3-clear)
```

## on-curve-bit3-set

```
-- builtin/semantics/bls12_381_G2_uncompress/on-curve-bit3-set
-- This value was obtained by hashing 0x0102030405 to G2.  No changes have been
-- made, so uncompression should succeed.
test-on-curve-bit3-set : Untyped
test-on-curve-bit3-set = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\168\DC3\142\190\167f\212\209\170d\221;X&$L2\234?\233\&5\US\156\141XB\ETXqm\174\NAK\GS\DC4\187]\ACK\226E\194Hw\149\\y(v\130\186\b-\a{\187*\253\177\173\GSH\209\142/\fV\176\SOH\188\226\a\128\SUB\223\169\253E\US\197\157V\240C;\STX\249!\186Z',X\192e6)\GS\a")))))

expected-on-curve-bit3-set : Result
expected-on-curve-bit3-set = success (UCon (tagCon bytestring (mkByteString "\168\DC3\142\190\167f\212\209\170d\221;X&$L2\234?\233\&5\US\156\141XB\ETXqm\174\NAK\GS\DC4\187]\ACK\226E\194Hw\149\\y(v\130\186\b-\a{\187*\253\177\173\GSH\209\142/\fV\176\SOH\188\226\a\128\SUB\223\169\253E\US\197\157V\240C;\STX\249!\186Z',X\192e6)\GS\a")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-uncompress`.
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
test-on-curve-serialised-not-compressed = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\b\DC3\142\190\167f\212\209\170d\221;X&$L2\234?\233\&5\US\156\141XB\ETXqm\174\NAK\GS\DC4\187]\ACK\226E\194Hw\149\\y(v\130\186\b-\a{\187*\253\177\173\GSH\209\142/\fV\176\SOH\188\226\a\128\SUB\223\169\253E\US\197\157V\240C;\STX\249!\186Z',X\192e6)\GS\a\SYNv\178u\226p`\178m\217\SUB\172\n\US\235V\209\193\222|2?HnH\213N\174\f<\143L\170E\250\173X\156]\CAN\n\192\131\r\205\179\236\216\DC2l\156]\184l\223q)\207\CANX \DC3\210g\167\194\130z\144\RS\246\SUB\181\142~\241P!\148A\171\197vq\235\&9\NUL\159k\177f\188\186\222p\r"))))

expected-on-curve-serialised-not-compressed : Result
expected-on-curve-serialised-not-compressed = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
pending-on-curve-serialised-not-compressed : Set
pending-on-curve-serialised-not-compressed = Pending (evalRaw test-on-curve-serialised-not-compressed ≡ expected-on-curve-serialised-not-compressed)
```

## out-of-group

```
-- builtin/semantics/bls12_381_G2_uncompress/out-of-group
-- This contains a value which is the x-coordinate of a point which lies on the
-- E2 curve but not the G2 subgroup.
test-out-of-group : Untyped
test-out-of-group = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\160\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\ENQ"))))

expected-out-of-group : Result
expected-out-of-group = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
pending-out-of-group : Set
pending-out-of-group = Pending (evalRaw test-out-of-group ≡ expected-out-of-group)
```

## too-long

```
-- builtin/semantics/bls12_381_G2_uncompress/too-long
-- The bytestring is the compressed version of the G2 zero point, but extended to 97 bytes.
test-too-long : Untyped
test-too-long = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))

expected-too-long : Result
expected-too-long = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
pending-too-long : Set
pending-too-long = Pending (evalRaw test-too-long ≡ expected-too-long)
```

## too-short

```
-- builtin/semantics/bls12_381_G2_uncompress/too-short
-- The bytestring is the compressed version of the G2 zero point, but truncated to 94 bytes.
test-too-short : Untyped
test-too-short = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))

expected-too-short : Result
expected-too-short = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
pending-too-short : Set
pending-too-short = Pending (evalRaw test-too-short ≡ expected-too-short)
```

## zero

```
-- builtin/semantics/bls12_381_G2_uncompress/zero
-- The zero element of G2 uncompresses correctly.
test-zero : Untyped
test-zero = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))))

expected-zero : Result
expected-zero = success (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-uncompress`.
pending-zero : Set
pending-zero = Pending (evalRaw test-zero ≡ expected-zero)
```
