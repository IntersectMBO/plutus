---
title: Conformance.Builtin.Semantics.Bls12381G2ScalarMul
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G2_scalarMul`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G2ScalarMul where

open import Conformance.Eval
```

## addmul

```
-- builtin/semantics/bls12_381_G2_scalarMul/addmul
-- 2157p + 2157q for random points p and q in G2.  This should give the same result as muladd.
test-addmul : Untyped
test-addmul = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))))

expected-addmul : Result
expected-addmul = success (UCon (tagCon bytestring (mkByteString "b8a335cdbb3de744ba2b6bb3c9ad9c209a7f33a1453c2ed0460e188c1f31f185e359a62727fe1d8ba5c931d75ef644e50173e5255b62194677fb67323ce42bac5c6b1b077e682df3aabca1caee2f640db1fed0b4ad511562f7c54d84ea76debc")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-addmul : Set
pending-addmul = Pending (evalRaw test-addmul ≡ expected-addmul)
```

## mul-44

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul-44
-- Check that multiplication by the scalar 44 gives the expected result.
test-mul-44 : Untyped
test-mul-44 = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 44)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))))

expected-mul-44 : Result
expected-mul-44 = success (UCon (tagCon bytestring (mkByteString "aa2a95bc9936c61f5039cc6fbbe0e25fa8b1528ea18c5be09c93ed941d1c9052597086b8d3b3b5fbbd110ce389378c5414efd310de2120a7efbaaf70d01f5b80835118c1f39a4273a10f1f2a4af0ed33a7c17fba4c8e3f7cb08a1d97e82d5611")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul-44 : Set
pending-mul-44 = Pending (evalRaw test-mul-44 ≡ expected-mul-44)
```

## mul-neg-one

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul-neg-one
-- Check that the result of multiplying by -1 is as expected.
test-mul-neg-one : Untyped
test-mul-neg-one = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.negsuc 0)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))))

expected-mul-neg-one : Result
expected-mul-neg-one = success (UCon (tagCon bytestring (mkByteString "a310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul-neg-one : Set
pending-mul-neg-one = Pending (evalRaw test-mul-neg-one ≡ expected-mul-neg-one)
```

## mul-one

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul-one
-- Scalar multiplication by 1 leaves a random point unchanged.
test-mul-one : Untyped
test-mul-one = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 1)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))))

expected-mul-one : Result
expected-mul-one = success (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul-one : Set
pending-mul-one = Pending (evalRaw test-mul-one ≡ expected-mul-one)
```

## mul-zero

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul-zero
-- Multiplication by the zero scalar gives the zero point of G2.
test-mul-zero : Untyped
test-mul-zero = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 0)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))))

expected-mul-zero : Result
expected-mul-zero = success (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul-zero : Set
pending-mul-zero = Pending (evalRaw test-mul-zero ≡ expected-mul-zero)
```

## mul19+25

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul19+25
-- 19p+25p for a random point p in G2.  This should give the same result as mul44.
test-mul19-25 : Untyped
test-mul19-25 = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 19)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 25)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))))

expected-mul19-25 : Result
expected-mul19-25 = success (UCon (tagCon bytestring (mkByteString "aa2a95bc9936c61f5039cc6fbbe0e25fa8b1528ea18c5be09c93ed941d1c9052597086b8d3b3b5fbbd110ce389378c5414efd310de2120a7efbaaf70d01f5b80835118c1f39a4273a10f1f2a4af0ed33a7c17fba4c8e3f7cb08a1d97e82d5611")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul19-25 : Set
pending-mul19-25 = Pending (evalRaw test-mul19-25 ≡ expected-mul19-25)
```

## mul4x-11

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul4x-11
-- 4*(11*p) for a point in G2.  This should give the same result as mul44.
test-mul4x-11 : Untyped
test-mul4x-11 = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 4)))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 11)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))))

expected-mul4x-11 : Result
expected-mul4x-11 = success (UCon (tagCon bytestring (mkByteString "aa2a95bc9936c61f5039cc6fbbe0e25fa8b1528ea18c5be09c93ed941d1c9052597086b8d3b3b5fbbd110ce389378c5414efd310de2120a7efbaaf70d01f5b80835118c1f39a4273a10f1f2a4af0ed33a7c17fba4c8e3f7cb08a1d97e82d5611")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul4x-11 : Set
pending-mul4x-11 = Pending (evalRaw test-mul4x-11 ≡ expected-mul4x-11)
```

## muladd

```
-- builtin/semantics/bls12_381_G2_scalarMul/muladd
-- n(p+q) = np + nq (n scalar, p and q random points in G2).
test-muladd : Untyped
test-muladd = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))))

expected-muladd : Result
expected-muladd = success (UCon (tagCon bytestring (mkByteString "b8a335cdbb3de744ba2b6bb3c9ad9c209a7f33a1453c2ed0460e188c1f31f185e359a62727fe1d8ba5c931d75ef644e50173e5255b62194677fb67323ce42bac5c6b1b077e682df3aabca1caee2f640db1fed0b4ad511562f7c54d84ea76debc")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
pending-muladd : Set
pending-muladd = Pending (evalRaw test-muladd ≡ expected-muladd)
```

## mulneg-44

```
-- builtin/semantics/bls12_381_G2_scalarMul/mulneg-44
-- Multiplying a random point in G2 by the scalar -44 gives the expected result.
test-mulneg-44 : Untyped
test-mulneg-44 = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.negsuc 43)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))))

expected-mulneg-44 : Result
expected-mulneg-44 = success (UCon (tagCon bytestring (mkByteString "8a2a95bc9936c61f5039cc6fbbe0e25fa8b1528ea18c5be09c93ed941d1c9052597086b8d3b3b5fbbd110ce389378c5414efd310de2120a7efbaaf70d01f5b80835118c1f39a4273a10f1f2a4af0ed33a7c17fba4c8e3f7cb08a1d97e82d5611")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mulneg-44 : Set
pending-mulneg-44 = Pending (evalRaw test-mulneg-44 ≡ expected-mulneg-44)
```

## mulperiodic-01

```
-- builtin/semantics/bls12_381_G2_scalarMul/mulperiodic-01
-- Scalar multiplication by the group size should give you the zero element of the group.
test-mulperiodic-01 : Untyped
test-mulperiodic-01 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))))) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))

expected-mulperiodic-01 : Result
expected-mulperiodic-01 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mulperiodic-01 : Set
pending-mulperiodic-01 = Pending (evalRaw test-mulperiodic-01 ≡ expected-mulperiodic-01)
```

## mulperiodic-02

```
-- builtin/semantics/bls12_381_G2_scalarMul/mulperiodic-02
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-02 : Untyped
test-mulperiodic-02 = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))))

expected-mulperiodic-02 : Result
expected-mulperiodic-02 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mulperiodic-02 : Set
pending-mulperiodic-02 = Pending (evalRaw test-mulperiodic-02 ≡ expected-mulperiodic-02)
```

## mulperiodic-03

```
-- builtin/semantics/bls12_381_G2_scalarMul/mulperiodic-03
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-03 : Untyped
test-mulperiodic-03 = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 987654321)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))))

expected-mulperiodic-03 : Result
expected-mulperiodic-03 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mulperiodic-03 : Set
pending-mulperiodic-03 = Pending (evalRaw test-mulperiodic-03 ≡ expected-mulperiodic-03)
```

## mulperiodic-04

```
-- builtin/semantics/bls12_381_G2_scalarMul/mulperiodic-04
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-04 : Untyped
test-mulperiodic-04 = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.negsuc 987654320)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))))

expected-mulperiodic-04 : Result
expected-mulperiodic-04 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mulperiodic-04 : Set
pending-mulperiodic-04 = Pending (evalRaw test-mulperiodic-04 ≡ expected-mulperiodic-04)
```
