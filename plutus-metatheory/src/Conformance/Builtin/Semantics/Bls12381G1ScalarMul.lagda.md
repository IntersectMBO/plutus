---
title: Conformance.Builtin.Semantics.Bls12381G1ScalarMul
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G1_scalarMul`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G1ScalarMul where

open import Conformance.Eval
```

## addmul

```
-- builtin/semantics/bls12_381_G1_scalarMul/addmul
-- 2157p + 2157q for random points p and q in G1.  This should give the same result as muladd.
test-addmul : Untyped
test-addmul = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245")))))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))))))

expected-addmul : Result
expected-addmul = success (UCon (tagCon bytestring (mkByteString "\140\200Fy\198\200p@\129i\166V\194E\162\171\156\204FY\135i\177\159\aq\FS\CANbB\132\209\191\163\&6g\202\199\185\154\DC2\224X\171\253\DC4\239\136")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-addmul : Set
pending-addmul = Pending (evalRaw test-addmul ≡ expected-addmul)
```

## mul-44

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul-44
-- Check that multiplication by the scalar 44 gives the expected result.
test-mul-44 : Untyped
test-mul-44 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 44)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))

expected-mul-44 : Result
expected-mul-44 = success (UCon (tagCon bytestring (mkByteString "\141\158\159j\220\234\DC4\232\211\130!\187<\254J\253\204Y\184n\157;\NUL\147\192\239\130R\213\217\r\252]s\201\233\211R\185\165KF\211^\DEL\244\213\140")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul-44 : Set
pending-mul-44 = Pending (evalRaw test-mul-44 ≡ expected-mul-44)
```

## mul-neg-one

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul-neg-one
-- Check that the result of multiplying by -1 is as expected.
test-mul-neg-one : Untyped
test-mul-neg-one = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.negsuc 0)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))

expected-mul-neg-one : Result
expected-mul-neg-one = success (UCon (tagCon bytestring (mkByteString "\139\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul-neg-one : Set
pending-mul-neg-one = Pending (evalRaw test-mul-neg-one ≡ expected-mul-neg-one)
```

## mul-one

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul-one
-- Scalar multiplication by 1 leaves a random point unchanged.
test-mul-one : Untyped
test-mul-one = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 1)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))

expected-mul-one : Result
expected-mul-one = success (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul-one : Set
pending-mul-one = Pending (evalRaw test-mul-one ≡ expected-mul-one)
```

## mul-zero

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul-zero
-- Multiplication by the zero scalar gives the zero point of G1.
test-mul-zero : Untyped
test-mul-zero = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 0)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))

expected-mul-zero : Result
expected-mul-zero = success (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul-zero : Set
pending-mul-zero = Pending (evalRaw test-mul-zero ≡ expected-mul-zero)
```

## mul19+25

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul19+25
-- 19p+25p for a random point p in G1.  This should give the same result as mul44.
test-mul19-25 : Untyped
test-mul19-25 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 19)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 25)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))))))

expected-mul19-25 : Result
expected-mul19-25 = success (UCon (tagCon bytestring (mkByteString "\141\158\159j\220\234\DC4\232\211\130!\187<\254J\253\204Y\184n\157;\NUL\147\192\239\130R\213\217\r\252]s\201\233\211R\185\165KF\211^\DEL\244\213\140")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul19-25 : Set
pending-mul19-25 = Pending (evalRaw test-mul19-25 ≡ expected-mul19-25)
```

## mul4x-11

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul4x-11
-- 4*(11*p) for a point in G1.  This should give the same result as mul44.
test-mul4x-11 : Untyped
test-mul4x-11 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 4)))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 11)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))))))

expected-mul4x-11 : Result
expected-mul4x-11 = success (UCon (tagCon bytestring (mkByteString "\141\158\159j\220\234\DC4\232\211\130!\187<\254J\253\204Y\184n\157;\NUL\147\192\239\130R\213\217\r\252]s\201\233\211R\185\165KF\211^\DEL\244\213\140")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul4x-11 : Set
pending-mul4x-11 = Pending (evalRaw test-mul4x-11 ≡ expected-mul4x-11)
```

## muladd

```
-- builtin/semantics/bls12_381_G1_scalarMul/muladd
-- n(p+q) = np + nq (n scalar, p and q random points in G1).
test-muladd : Untyped
test-muladd = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))))))

expected-muladd : Result
expected-muladd = success (UCon (tagCon bytestring (mkByteString "\140\200Fy\198\200p@\129i\166V\194E\162\171\156\204FY\135i\177\159\aq\FS\CANbB\132\209\191\163\&6g\202\199\185\154\DC2\224X\171\253\DC4\239\136")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-muladd : Set
pending-muladd = Pending (evalRaw test-muladd ≡ expected-muladd)
```

## mulneg-44

```
-- builtin/semantics/bls12_381_G1_scalarMul/mulneg-44
-- Multiplying a random point in G1 by the scalar -44 gives the expected result.
test-mulneg-44 : Untyped
test-mulneg-44 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.negsuc 43)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))

expected-mulneg-44 : Result
expected-mulneg-44 = success (UCon (tagCon bytestring (mkByteString "\173\158\159j\220\234\DC4\232\211\130!\187<\254J\253\204Y\184n\157;\NUL\147\192\239\130R\213\217\r\252]s\201\233\211R\185\165KF\211^\DEL\244\213\140")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mulneg-44 : Set
pending-mulneg-44 = Pending (evalRaw test-mulneg-44 ≡ expected-mulneg-44)
```

## mulperiodic-01

```
-- builtin/semantics/bls12_381_G1_scalarMul/mulperiodic-01
-- Scalar multiplication by the group size should give you the zero element of the group.
test-mulperiodic-01 : Untyped
test-mulperiodic-01 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))

expected-mulperiodic-01 : Result
expected-mulperiodic-01 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mulperiodic-01 : Set
pending-mulperiodic-01 = Pending (evalRaw test-mulperiodic-01 ≡ expected-mulperiodic-01)
```

## mulperiodic-02

```
-- builtin/semantics/bls12_381_G1_scalarMul/mulperiodic-02
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-02 : Untyped
test-mulperiodic-02 = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))

expected-mulperiodic-02 : Result
expected-mulperiodic-02 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mulperiodic-02 : Set
pending-mulperiodic-02 = Pending (evalRaw test-mulperiodic-02 ≡ expected-mulperiodic-02)
```

## mulperiodic-03

```
-- builtin/semantics/bls12_381_G1_scalarMul/mulperiodic-03
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-03 : Untyped
test-mulperiodic-03 = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 987654321)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))

expected-mulperiodic-03 : Result
expected-mulperiodic-03 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mulperiodic-03 : Set
pending-mulperiodic-03 = Pending (evalRaw test-mulperiodic-03 ≡ expected-mulperiodic-03)
```

## mulperiodic-04

```
-- builtin/semantics/bls12_381_G1_scalarMul/mulperiodic-04
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-04 : Untyped
test-mulperiodic-04 = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.negsuc 987654320)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))

expected-mulperiodic-04 : Result
expected-mulperiodic-04 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mulperiodic-04 : Set
pending-mulperiodic-04 = Pending (evalRaw test-mulperiodic-04 ≡ expected-mulperiodic-04)
```
