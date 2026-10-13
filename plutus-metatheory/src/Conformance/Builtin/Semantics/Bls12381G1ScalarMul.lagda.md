---
title: Conformance.Builtin.Semantics.Bls12381G1ScalarMul
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

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
test-addmul = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5")))))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))))

expected-addmul : Result
expected-addmul = success (UCon (tagCon bytestring (mkByteString "8cc84679c6c870408169a656c245a2ab9ccc46598769b19f07711c18624284d1bfa33667cac7b99a12e058abfd14ef88")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-addmul : Set
pending-addmul = Pending (evalRaw test-addmul ≡ expected-addmul)
```

## mul-44

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul-44
-- Check that multiplication by the scalar 44 gives the expected result.
test-mul-44 : Untyped
test-mul-44 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 44)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))

expected-mul-44 : Result
expected-mul-44 = success (UCon (tagCon bytestring (mkByteString "8d9e9f6adcea14e8d38221bb3cfe4afdcc59b86e9d3b0093c0ef8252d5d90dfc5d73c9e9d352b9a54b46d35e7ff4d58c")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul-44 : Set
pending-mul-44 = Pending (evalRaw test-mul-44 ≡ expected-mul-44)
```

## mul-neg-one

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul-neg-one
-- Check that the result of multiplying by -1 is as expected.
test-mul-neg-one : Untyped
test-mul-neg-one = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.negsuc 0)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))

expected-mul-neg-one : Result
expected-mul-neg-one = success (UCon (tagCon bytestring (mkByteString "8bd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul-neg-one : Set
pending-mul-neg-one = Pending (evalRaw test-mul-neg-one ≡ expected-mul-neg-one)
```

## mul-one

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul-one
-- Scalar multiplication by 1 leaves a random point unchanged.
test-mul-one : Untyped
test-mul-one = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 1)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))

expected-mul-one : Result
expected-mul-one = success (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul-one : Set
pending-mul-one = Pending (evalRaw test-mul-one ≡ expected-mul-one)
```

## mul-zero

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul-zero
-- Multiplication by the zero scalar gives the zero point of G1.
test-mul-zero : Untyped
test-mul-zero = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 0)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))

expected-mul-zero : Result
expected-mul-zero = success (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul-zero : Set
pending-mul-zero = Pending (evalRaw test-mul-zero ≡ expected-mul-zero)
```

## mul19+25

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul19+25
-- 19p+25p for a random point p in G1.  This should give the same result as mul44.
test-mul19-25 : Untyped
test-mul19-25 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 19)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 25)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))))

expected-mul19-25 : Result
expected-mul19-25 = success (UCon (tagCon bytestring (mkByteString "8d9e9f6adcea14e8d38221bb3cfe4afdcc59b86e9d3b0093c0ef8252d5d90dfc5d73c9e9d352b9a54b46d35e7ff4d58c")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul19-25 : Set
pending-mul19-25 = Pending (evalRaw test-mul19-25 ≡ expected-mul19-25)
```

## mul4x-11

```
-- builtin/semantics/bls12_381_G1_scalarMul/mul4x-11
-- 4*(11*p) for a point in G1.  This should give the same result as mul44.
test-mul4x-11 : Untyped
test-mul4x-11 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 4)))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 11)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))))

expected-mul4x-11 : Result
expected-mul4x-11 = success (UCon (tagCon bytestring (mkByteString "8d9e9f6adcea14e8d38221bb3cfe4afdcc59b86e9d3b0093c0ef8252d5d90dfc5d73c9e9d352b9a54b46d35e7ff4d58c")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mul4x-11 : Set
pending-mul4x-11 = Pending (evalRaw test-mul4x-11 ≡ expected-mul4x-11)
```

## muladd

```
-- builtin/semantics/bls12_381_G1_scalarMul/muladd
-- n(p+q) = np + nq (n scalar, p and q random points in G1).
test-muladd : Untyped
test-muladd = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))))

expected-muladd : Result
expected-muladd = success (UCon (tagCon bytestring (mkByteString "8cc84679c6c870408169a656c245a2ab9ccc46598769b19f07711c18624284d1bfa33667cac7b99a12e058abfd14ef88")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-muladd : Set
pending-muladd = Pending (evalRaw test-muladd ≡ expected-muladd)
```

## mulneg-44

```
-- builtin/semantics/bls12_381_G1_scalarMul/mulneg-44
-- Multiplying a random point in G1 by the scalar -44 gives the expected result.
test-mulneg-44 : Untyped
test-mulneg-44 = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.negsuc 43)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))

expected-mulneg-44 : Result
expected-mulneg-44 = success (UCon (tagCon bytestring (mkByteString "ad9e9f6adcea14e8d38221bb3cfe4afdcc59b86e9d3b0093c0ef8252d5d90dfc5d73c9e9d352b9a54b46d35e7ff4d58c")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mulneg-44 : Set
pending-mulneg-44 = Pending (evalRaw test-mulneg-44 ≡ expected-mulneg-44)
```

## mulperiodic-01

```
-- builtin/semantics/bls12_381_G1_scalarMul/mulperiodic-01
-- Scalar multiplication by the group size should give you the zero element of the group.
test-mulperiodic-01 : Untyped
test-mulperiodic-01 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))

expected-mulperiodic-01 : Result
expected-mulperiodic-01 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mulperiodic-01 : Set
pending-mulperiodic-01 = Pending (evalRaw test-mulperiodic-01 ≡ expected-mulperiodic-01)
```

## mulperiodic-02

```
-- builtin/semantics/bls12_381_G1_scalarMul/mulperiodic-02
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-02 : Untyped
test-mulperiodic-02 = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))

expected-mulperiodic-02 : Result
expected-mulperiodic-02 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mulperiodic-02 : Set
pending-mulperiodic-02 = Pending (evalRaw test-mulperiodic-02 ≡ expected-mulperiodic-02)
```

## mulperiodic-03

```
-- builtin/semantics/bls12_381_G1_scalarMul/mulperiodic-03
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-03 : Untyped
test-mulperiodic-03 = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 987654321)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))

expected-mulperiodic-03 : Result
expected-mulperiodic-03 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mulperiodic-03 : Set
pending-mulperiodic-03 = Pending (evalRaw test-mulperiodic-03 ≡ expected-mulperiodic-03)
```

## mulperiodic-04

```
-- builtin/semantics/bls12_381_G1_scalarMul/mulperiodic-04
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-04 : Untyped
test-mulperiodic-04 = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.negsuc 987654320)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))

expected-mulperiodic-04 : Result
expected-mulperiodic-04 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-mulperiodic-04 : Set
pending-mulperiodic-04 = Pending (evalRaw test-mulperiodic-04 ≡ expected-mulperiodic-04)
```
