---
title: Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G2.Arith
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381-cardano-crypto-tests/G2/arith`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G2.Arith where

open import Conformance.Eval
```

## add

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/arith/add
-- Check that adding two random points in G2 gives the expected result.
test-add : Untyped
test-add = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b5ed6482bf5486831a9eb445b8b9a77aa6330005b8b432523c69fee7085d3032856de9f857c55ac9745eabcf14894205149cc67393687289e6c2728be69ad1f8ea1a6c0a5a65bf93eca984f3dac5da1abc6f7156ccbc5a33c655f7b17724eb19"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a6cc0f01663fd65a95d1359758ebe3a412ce05f4242b0c1f5964351b38e188362a8ceb6c2f86d3f7e5f73b60cd04288005d2a50f8ddf1751d7a915515054276fbae7569c3f18c614c9954177d8e745e98404654cf759d4747b0c806bbd336b7d"))))))) (UCon (tagCon bytestring (mkByteString "b3db03681aaf0d218be32f7cc94bd6a975c6870b4a1d4e461b77b60eee2461ca367154b0c4583b2d5f81124aa21fdf3e09ff6b54ce7c57572283a175fba381a32ac6f46abaf11cdbaeb206dcd7d4269caa4d0ebbb3adc1b8fce42ccfa855ea83"))))

expected-add : Result
expected-add = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
pending-add : Set
pending-add = Pending (evalRaw test-add ≡ expected-add)
```

## neg

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/arith/neg
-- Check that negating a random point in G2 gives the expected result.
test-neg : Untyped
test-neg = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-neg) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b5ed6482bf5486831a9eb445b8b9a77aa6330005b8b432523c69fee7085d3032856de9f857c55ac9745eabcf14894205149cc67393687289e6c2728be69ad1f8ea1a6c0a5a65bf93eca984f3dac5da1abc6f7156ccbc5a33c655f7b17724eb19"))))))) (UCon (tagCon bytestring (mkByteString "95ed6482bf5486831a9eb445b8b9a77aa6330005b8b432523c69fee7085d3032856de9f857c55ac9745eabcf14894205149cc67393687289e6c2728be69ad1f8ea1a6c0a5a65bf93eca984f3dac5da1abc6f7156ccbc5a33c655f7b17724eb19"))))

expected-neg : Result
expected-neg = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-neg`; postulated builtin `bls12-381-G2-uncompress`.
pending-neg : Set
pending-neg = Pending (evalRaw test-neg ≡ expected-neg)
```

## scalarMul

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/arith/scalarMul
-- Scalar multiplication gives the correct result.
test-scalarMul : Untyped
test-scalarMul = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 29342537169447282925541144552701591957563885683358707334406144036950193508773)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a6cc0f01663fd65a95d1359758ebe3a412ce05f4242b0c1f5964351b38e188362a8ceb6c2f86d3f7e5f73b60cd04288005d2a50f8ddf1751d7a915515054276fbae7569c3f18c614c9954177d8e745e98404654cf759d4747b0c806bbd336b7d"))))))) (UCon (tagCon bytestring (mkByteString "89b8e839c317ab3c735c6a65122fff4654f469c30c480701f6e4d9f311f3c5f3411c7cd2876c539bf56f983d14e550b5172765f62bba1235394a33413c21667a57214e9a6f2516f8d7bf57321c20bf8cd8ecd290691ad6bd5ab9e391304240a4"))))

expected-scalarMul : Result
expected-scalarMul = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-scalarMul : Set
pending-scalarMul = Pending (evalRaw test-scalarMul ≡ expected-scalarMul)
```
