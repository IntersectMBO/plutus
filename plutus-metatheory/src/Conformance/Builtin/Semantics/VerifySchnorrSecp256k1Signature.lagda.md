---
title: Conformance.Builtin.Semantics.VerifySchnorrSecp256k1Signature
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/verifySchnorrSecp256k1Signature`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.VerifySchnorrSecp256k1Signature where

open import Conformance.Eval
```

## long-key

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/long-key
test-long-key : Untyped
test-long-key = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f0101")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))

expected-long-key : Result
expected-long-key = failure

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-long-key : Set
pending-long-key = Pending (evalRaw test-long-key ≡ expected-long-key)
```

## long-sig

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/long-sig
test-long-sig : Untyped
test-long-sig = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c0909"))))

expected-long-sig : Result
expected-long-sig = failure

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-long-sig : Set
pending-long-sig = Pending (evalRaw test-long-sig ≡ expected-long-sig)
```

## short-key

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/short-key
test-short-key : Untyped
test-short-key = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))

expected-short-key : Result
expected-short-key = failure

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-short-key : Set
pending-short-key = Pending (evalRaw test-short-key ≡ expected-short-key)
```

## short-sig

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/short-sig
test-short-sig : Untyped
test-short-sig = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c"))))

expected-short-sig : Result
expected-short-sig = failure

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-short-sig : Set
pending-short-sig = Pending (evalRaw test-short-sig ≡ expected-short-sig)
```

## test-vector-00

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-00
-- Test vector 0 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
test-test-vector-00 : Untyped
test-test-vector-00 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9")))) (UCon (tagCon bytestring (mkByteString "0000000000000000000000000000000000000000000000000000000000000000")))) (UCon (tagCon bytestring (mkByteString "e907831f80848d1069a5371b402410364bdf1c5f8307b0084c55f1ce2dca821525f66a4a85ea8b71e482a74f382d2ce5ebeee8fdb2172f477df4900d310536c0"))))

expected-test-vector-00 : Result
expected-test-vector-00 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-00 : Set
pending-test-vector-00 = Pending (evalRaw test-test-vector-00 ≡ expected-test-vector-00)
```

## test-vector-01

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-01
-- Test vector 1 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
test-test-vector-01 : Untyped
test-test-vector-01 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "6896bd60eeae296db48a229ff71dfe071bde413e6d43f917dc8dcf8c78de33418906d11ac976abccb20b091292bff4ea897efcb639ea871cfa95f6de339e4b0a"))))

expected-test-vector-01 : Result
expected-test-vector-01 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-01 : Set
pending-test-vector-01 = Pending (evalRaw test-test-vector-01 ≡ expected-test-vector-01)
```

## test-vector-02

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-02
-- Test vector 2 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
test-test-vector-02 : Untyped
test-test-vector-02 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "dd308afec5777e13121fa72b9cc1b7cc0139715309b086c960e18fd969774eb8")))) (UCon (tagCon bytestring (mkByteString "7e2d58d8b3bcdf1abadec7829054f90dda9805aab56c77333024b9d0a508b75c")))) (UCon (tagCon bytestring (mkByteString "5831aaeed7b44bb74e5eab94ba9d4294c49bcf2a60728d8b4c200f50dd313c1bab745879a5ad954a72c45a91c3a51d3c7adea98d82f8481e0e1e03674a6f3fb7"))))

expected-test-vector-02 : Result
expected-test-vector-02 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-02 : Set
pending-test-vector-02 = Pending (evalRaw test-test-vector-02 ≡ expected-test-vector-02)
```

## test-vector-03

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-03
-- Test vector 3 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (test fails if msg is reduced modulo p or n)
test-test-vector-03 : Untyped
test-test-vector-03 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "25d1dff95105f5253c4022f628a996ad3a0d95fbf21d468a1b33f8c160d8f517")))) (UCon (tagCon bytestring (mkByteString "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")))) (UCon (tagCon bytestring (mkByteString "7eb0509757e246f19449885651611cb965ecc1a187dd51b64fda1edc9637d5ec97582b9cb13db3933705b32ba982af5af25fd78881ebb32771fc5922efc66ea3"))))

expected-test-vector-03 : Result
expected-test-vector-03 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-03 : Set
pending-test-vector-03 = Pending (evalRaw test-test-vector-03 ≡ expected-test-vector-03)
```

## test-vector-04

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-04
-- Test vector 4 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
test-test-vector-04 : Untyped
test-test-vector-04 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "d69c3509bb99e412e68b0fe8544e72837dfa30746d8be2aa65975f29d22dc7b9")))) (UCon (tagCon bytestring (mkByteString "4df3c3f68fcc83b27e9d42c90431a72499f17875c81a599b566c9889b9696703")))) (UCon (tagCon bytestring (mkByteString "00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c6376afb1548af603b3eb45c9f8207dee1060cb71c04e80f593060b07d28308d7f4"))))

expected-test-vector-04 : Result
expected-test-vector-04 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-04 : Set
pending-test-vector-04 = Pending (evalRaw test-test-vector-04 ≡ expected-test-vector-04)
```

## test-vector-05

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-05
-- Test vector 5 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect failure (public key not on the curve)
test-test-vector-05 : Untyped
test-test-vector-05 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "eefdea4cdb677750a420fee807eacf21eb9898ae79b9768766e4faa04a2d4a34")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "6cff5c3ba86c69ea4b7376f31a9bcb4f74c1976089b2d9963da2e5543e17776969e89b4c5564d00349106b8497785dd7d1d713a8ae82b32fa79d5f7fc407d39b"))))

expected-test-vector-05 : Result
expected-test-vector-05 = failure

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-05 : Set
pending-test-vector-05 = Pending (evalRaw test-test-vector-05 ≡ expected-test-vector-05)
```

## test-vector-06

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-06
-- Test vector 6 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (has_even_y(R) is false)
test-test-vector-06 : Untyped
test-test-vector-06 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a14602975563cc27944640ac607cd107ae10923d9ef7a73c643e166be5ebeafa34b1ac553e2"))))

expected-test-vector-06 : Result
expected-test-vector-06 = success (UCon (tagCon bool false))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-06 : Set
pending-test-vector-06 = Pending (evalRaw test-test-vector-06 ≡ expected-test-vector-06)
```

## test-vector-07

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-07
-- Test vector 7 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (negated message)
test-test-vector-07 : Untyped
test-test-vector-07 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "1fa62e331edbc21c394792d2ab1100a7b432b013df3f6ff4f99fcb33e0e1515f28890b3edb6e7189b630448b515ce4f8622a954cfe545735aaea5134fccdb2bd"))))

expected-test-vector-07 : Result
expected-test-vector-07 = success (UCon (tagCon bool false))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-07 : Set
pending-test-vector-07 = Pending (evalRaw test-test-vector-07 ≡ expected-test-vector-07)
```

## test-vector-08

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-08
-- Test vector 8 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (negated s value)
test-test-vector-08 : Untyped
test-test-vector-08 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "6cff5c3ba86c69ea4b7376f31a9bcb4f74c1976089b2d9963da2e5543e177769961764b3aa9b2ffcb6ef947b6887a226e8d7c93e00c5ed0c1834ff0d0c2e6da6"))))

expected-test-vector-08 : Result
expected-test-vector-08 = success (UCon (tagCon bool false))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-08 : Set
pending-test-vector-08 = Pending (evalRaw test-test-vector-08 ≡ expected-test-vector-08)
```

## test-vector-09

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-09
-- Test vector 9 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False
-- (sG - eP is infinite. Test fails in single verification if has_even_y(inf) is defined as true and x(inf) as 0)
test-test-vector-09 : Untyped
test-test-vector-09 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "0000000000000000000000000000000000000000000000000000000000000000123dda8328af9c23a94c1feecfd123ba4fb73476f0d594dcb65c6425bd186051"))))

expected-test-vector-09 : Result
expected-test-vector-09 = success (UCon (tagCon bool false))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-09 : Set
pending-test-vector-09 = Pending (evalRaw test-test-vector-09 ≡ expected-test-vector-09)
```

## test-vector-10

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-10
-- Test vector 10 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False
-- (sG - eP is infinite. Test fails in single verification if has_even_y(inf) is defined as true and x(inf) as 1)
test-test-vector-10 : Untyped
test-test-vector-10 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "00000000000000000000000000000000000000000000000000000000000000017615fbaf5ae28864013c099742deadb4dba87f11ac6754f93780d5a1837cf197"))))

expected-test-vector-10 : Result
expected-test-vector-10 = success (UCon (tagCon bool false))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-10 : Set
pending-test-vector-10 = Pending (evalRaw test-test-vector-10 ≡ expected-test-vector-10)
```

## test-vector-11

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-11
-- Test vector 11 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (sig[0:32] is not an X coordinate on the curve)
test-test-vector-11 : Untyped
test-test-vector-11 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "4a298dacae57395a15d0795ddbfd1dcb564da82b0f269bc70a74f8220429ba1d69e89b4c5564d00349106b8497785dd7d1d713a8ae82b32fa79d5f7fc407d39b"))))

expected-test-vector-11 : Result
expected-test-vector-11 = success (UCon (tagCon bool false))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-11 : Set
pending-test-vector-11 = Pending (evalRaw test-test-vector-11 ≡ expected-test-vector-11)
```

## test-vector-12

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-12
-- Test vector 12 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (sig[0:32] is equal to field size)
test-test-vector-12 : Untyped
test-test-vector-12 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f69e89b4c5564d00349106b8497785dd7d1d713a8ae82b32fa79d5f7fc407d39b"))))

expected-test-vector-12 : Result
expected-test-vector-12 = success (UCon (tagCon bool false))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-12 : Set
pending-test-vector-12 = Pending (evalRaw test-test-vector-12 ≡ expected-test-vector-12)
```

## test-vector-13

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-13
-- Test vector 13 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (sig[32:64] is equal to curve order)
test-test-vector-13 : Untyped
test-test-vector-13 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "6cff5c3ba86c69ea4b7376f31a9bcb4f74c1976089b2d9963da2e5543e177769fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"))))

expected-test-vector-13 : Result
expected-test-vector-13 = success (UCon (tagCon bool false))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-13 : Set
pending-test-vector-13 = Pending (evalRaw test-test-vector-13 ≡ expected-test-vector-13)
```

## test-vector-14

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-14
-- Test vector 14 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect failure (public key is not a valid X coordinate because it exceeds the field size)
test-test-vector-14 : Untyped
test-test-vector-14 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30")))) (UCon (tagCon bytestring (mkByteString "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89")))) (UCon (tagCon bytestring (mkByteString "6cff5c3ba86c69ea4b7376f31a9bcb4f74c1976089b2d9963da2e5543e17776969e89b4c5564d00349106b8497785dd7d1d713a8ae82b32fa79d5f7fc407d39b"))))

expected-test-vector-14 : Result
expected-test-vector-14 = failure

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-14 : Set
pending-test-vector-14 = Pending (evalRaw test-test-vector-14 ≡ expected-test-vector-14)
```

## test-vector-15

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-15
-- Test vector 15 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 0)
test-test-vector-15 : Untyped
test-test-vector-15 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "778caa53b4393ac467774d09497a87224bf9fab6f6e68b23086497324d6fd117")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "71535db165ecd9fbbc046e5ffaea61186bb6ad436732fccc25291a55895464cf6069ce26bf03466228f19a3a62db8a649f2d560fac652827d1af0574e427ab63"))))

expected-test-vector-15 : Result
expected-test-vector-15 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-15 : Set
pending-test-vector-15 = Pending (evalRaw test-test-vector-15 ≡ expected-test-vector-15)
```

## test-vector-16

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-16
-- Test vector 16 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 1 (added 2022-12)
test-test-vector-16 : Untyped
test-test-vector-16 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "778caa53b4393ac467774d09497a87224bf9fab6f6e68b23086497324d6fd117")))) (UCon (tagCon bytestring (mkByteString "11")))) (UCon (tagCon bytestring (mkByteString "08a20a0afef64124649232e0693c583ab1b9934ae63b4c3511f3ae1134c6a303ea3173bfea6683bd101fa5aa5dbc1996fe7cacfc5a577d33ec14564cec2bacbf"))))

expected-test-vector-16 : Result
expected-test-vector-16 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-16 : Set
pending-test-vector-16 = Pending (evalRaw test-test-vector-16 ≡ expected-test-vector-16)
```

## test-vector-17

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-17
-- Test vector 17 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 17)
test-test-vector-17 : Untyped
test-test-vector-17 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "778caa53b4393ac467774d09497a87224bf9fab6f6e68b23086497324d6fd117")))) (UCon (tagCon bytestring (mkByteString "0102030405060708090a0b0c0d0e0f1011")))) (UCon (tagCon bytestring (mkByteString "5130f39a4059b43bc7cac09a19ece52b5d8699d1a71e3c52da9afdb6b50ac370c4a482b77bf960f8681540e25b6771ece1e5a37fd80e5a51897c5566a97ea5a5"))))

expected-test-vector-17 : Result
expected-test-vector-17 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-17 : Set
pending-test-vector-17 = Pending (evalRaw test-test-vector-17 ≡ expected-test-vector-17)
```

## test-vector-18

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-18
-- Test vector 18 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 100)
test-test-vector-18 : Untyped
test-test-vector-18 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "778caa53b4393ac467774d09497a87224bf9fab6f6e68b23086497324d6fd117")))) (UCon (tagCon bytestring (mkByteString "99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999")))) (UCon (tagCon bytestring (mkByteString "403b12b0d8555a344175ea7ec746566303321e5dbfa8be6f091635163eca79a8585ed3e3170807e7c03b720fc54c7b23897fcba0e9d0b4a06894cfd249f22367"))))

expected-test-vector-18 : Result
expected-test-vector-18 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-18 : Set
pending-test-vector-18 = Pending (evalRaw test-test-vector-18 ≡ expected-test-vector-18)
```
