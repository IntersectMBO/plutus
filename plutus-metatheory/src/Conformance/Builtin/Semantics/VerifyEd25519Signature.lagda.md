---
title: Conformance.Builtin.Semantics.VerifyEd25519Signature
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/verifyEd25519Signature`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.VerifyEd25519Signature where

open import Conformance.Eval
```

## long-key

```
-- builtin/semantics/verifyEd25519Signature/long-key
test-long-key : Untyped
test-long-key = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f0101")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))

expected-long-key : Result
expected-long-key = failure

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-long-key : Set
pending-long-key = Pending (evalRaw test-long-key ≡ expected-long-key)
```

## long-sig

```
-- builtin/semantics/verifyEd25519Signature/long-sig
test-long-sig : Untyped
test-long-sig = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c0909"))))

expected-long-sig : Result
expected-long-sig = failure

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-long-sig : Set
pending-long-sig = Pending (evalRaw test-long-sig ≡ expected-long-sig)
```

## short-key

```
-- builtin/semantics/verifyEd25519Signature/short-key
test-short-key : Untyped
test-short-key = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))

expected-short-key : Result
expected-short-key = failure

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-short-key : Set
pending-short-key = Pending (evalRaw test-short-key ≡ expected-short-key)
```

## short-sig

```
-- builtin/semantics/verifyEd25519Signature/short-sig
test-short-sig : Untyped
test-short-sig = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c"))))

expected-short-sig : Result
expected-short-sig = failure

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-short-sig : Set
pending-short-sig = Pending (evalRaw test-short-sig ≡ expected-short-sig)
```

## test-vector-01

```
-- builtin/semantics/verifyEd25519Signature/test-vector-01
test-test-vector-01 : Untyped
test-test-vector-01 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"))))

expected-test-vector-01 : Result
expected-test-vector-01 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-01 : Set
pending-test-vector-01 = Pending (evalRaw test-test-vector-01 ≡ expected-test-vector-01)
```

## test-vector-02

```
-- builtin/semantics/verifyEd25519Signature/test-vector-02
test-test-vector-02 : Untyped
test-test-vector-02 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")))) (UCon (tagCon bytestring (mkByteString "72")))) (UCon (tagCon bytestring (mkByteString "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"))))

expected-test-vector-02 : Result
expected-test-vector-02 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-02 : Set
pending-test-vector-02 = Pending (evalRaw test-test-vector-02 ≡ expected-test-vector-02)
```

## test-vector-03

```
-- builtin/semantics/verifyEd25519Signature/test-vector-03
test-test-vector-03 : Untyped
test-test-vector-03 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025")))) (UCon (tagCon bytestring (mkByteString "af82")))) (UCon (tagCon bytestring (mkByteString "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a"))))

expected-test-vector-03 : Result
expected-test-vector-03 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-03 : Set
pending-test-vector-03 = Pending (evalRaw test-test-vector-03 ≡ expected-test-vector-03)
```

## test-vector-04

```
-- builtin/semantics/verifyEd25519Signature/test-vector-04
test-test-vector-04 : Untyped
test-test-vector-04 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e61a185bcef2613a6c7cb79763ce945d3b245d76114dd440bcf5f2dc1aa57057")))) (UCon (tagCon bytestring (mkByteString "cbc77b")))) (UCon (tagCon bytestring (mkByteString "d9868d52c2bebce5f3fa5a79891970f309cb6591e3e1702a70276fa97c24b3a8e58606c38c9758529da50ee31b8219cba45271c689afa60b0ea26c99db19b00c"))))

expected-test-vector-04 : Result
expected-test-vector-04 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-04 : Set
pending-test-vector-04 = Pending (evalRaw test-test-vector-04 ≡ expected-test-vector-04)
```

## test-vector-05

```
-- builtin/semantics/verifyEd25519Signature/test-vector-05
test-test-vector-05 : Untyped
test-test-vector-05 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "6df9340c138cc188b5fe4464ebaa3f7fc206a2d55c3434707e74c9fc04e20ebb")))) (UCon (tagCon bytestring (mkByteString "5f4c8989")))) (UCon (tagCon bytestring (mkByteString "124f6fc6b0d100842769e71bd530664d888df8507df6c56dedfdb509aeb93416e26b918d38aa06305df3095697c18b2aa832eaa52edc0ae49fbae5a85e150c07"))))

expected-test-vector-05 : Result
expected-test-vector-05 = success (UCon (tagCon bool false))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-05 : Set
pending-test-vector-05 = Pending (evalRaw test-test-vector-05 ≡ expected-test-vector-05)
```

## test-vector-06

```
-- builtin/semantics/verifyEd25519Signature/test-vector-06
test-test-vector-06 : Untyped
test-test-vector-06 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))

expected-test-vector-06 : Result
expected-test-vector-06 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-06 : Set
pending-test-vector-06 = Pending (evalRaw test-test-vector-06 ≡ expected-test-vector-06)
```

## test-vector-07

```
-- builtin/semantics/verifyEd25519Signature/test-vector-07
test-test-vector-07 : Untyped
test-test-vector-07 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "fbcfbfa40505d7f2be444a33d185cc54e16d615260e1640b2b5087b83ee3643d")))) (UCon (tagCon bytestring (mkByteString "89010d855972")))) (UCon (tagCon bytestring (mkByteString "6ed629fc1d9ce9e1468755ff636d5a3f40a5d9c91afd93b79d241830f7e5fa29854b8f20cc6eecbb248dbd8d16d14e99752194e4904d09c74d639518839d2300"))))

expected-test-vector-07 : Result
expected-test-vector-07 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-07 : Set
pending-test-vector-07 = Pending (evalRaw test-test-vector-07 ≡ expected-test-vector-07)
```

## test-vector-08

```
-- builtin/semantics/verifyEd25519Signature/test-vector-08
test-test-vector-08 : Untyped
test-test-vector-08 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "98a5e3a36e67aaba89888bf093de1ad963e774013b3902bfab356d8b90178a63")))) (UCon (tagCon bytestring (mkByteString "b4a8f381e70e7a")))) (UCon (tagCon bytestring (mkByteString "6e0af2fe55ae377a6b7a7278edfb419bd321e06d0df5e27037db8812e7e3529810fa5552f6c0020985ca17a0e02e036d7b222a24f99b77b75fdd16cb05568107"))))

expected-test-vector-08 : Result
expected-test-vector-08 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-08 : Set
pending-test-vector-08 = Pending (evalRaw test-test-vector-08 ≡ expected-test-vector-08)
```

## test-vector-09

```
-- builtin/semantics/verifyEd25519Signature/test-vector-09
test-test-vector-09 : Untyped
test-test-vector-09 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "f81fb54a825fced95eb033afcd64314075abfb0abd20a970892503436f34b863")))) (UCon (tagCon bytestring (mkByteString "4284abc51bb67235")))) (UCon (tagCon bytestring (mkByteString "d6addec5afb0528ac17bb178d3e7f2887f9adbb1ad16e110545ef3bc57f9de2314a5c8388f723b8907be0f3ac90c6259bbe885ecc17645df3db7d488f805fa08"))))

expected-test-vector-09 : Result
expected-test-vector-09 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-09 : Set
pending-test-vector-09 = Pending (evalRaw test-test-vector-09 ≡ expected-test-vector-09)
```

## test-vector-10

```
-- builtin/semantics/verifyEd25519Signature/test-vector-10
test-test-vector-10 : Untyped
test-test-vector-10 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "c1a49c66e617f9ef5ec66bc4c6564ca33de2a5fb5e1464062e6d6c6219155efd")))) (UCon (tagCon bytestring (mkByteString "672bf8965d04bc5146")))) (UCon (tagCon bytestring (mkByteString "2c76a04af2391c147082e33faacdbe56642a1e134bd388620b852b901a6bc16ff6c9cc9404c41dea12ed281da067a1513866f9d964f8bdd24953856c50042901"))))

expected-test-vector-10 : Result
expected-test-vector-10 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-10 : Set
pending-test-vector-10 = Pending (evalRaw test-test-vector-10 ≡ expected-test-vector-10)
```

## test-vector-11

```
-- builtin/semantics/verifyEd25519Signature/test-vector-11
test-test-vector-11 : Untyped
test-test-vector-11 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "31b2524b8348f7ab1dfafa675cc538e9a84e3fe5819e27c12ad8bbc1a36e4dff")))) (UCon (tagCon bytestring (mkByteString "33d7a786aded8c1bf691")))) (UCon (tagCon bytestring (mkByteString "28e4598c415ae9de01f03f9f3fab4e919e8bf537dd2b0cdf6e79b9e6559c9409d9151a4c40f083193937627c369488259e99da5a9f0a87497fa6696a5dd6ce08"))))

expected-test-vector-11 : Result
expected-test-vector-11 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-11 : Set
pending-test-vector-11 = Pending (evalRaw test-test-vector-11 ≡ expected-test-vector-11)
```

## test-vector-12

```
-- builtin/semantics/verifyEd25519Signature/test-vector-12
test-test-vector-12 : Untyped
test-test-vector-12 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "44b57ee30cdb55829d0a5d4f046baef078f1e97a7f21b62d75f8e96ea139c35f")))) (UCon (tagCon bytestring (mkByteString "3486f68848a65a0eb5507d")))) (UCon (tagCon bytestring (mkByteString "77d389e599630d934076329583cd4105a649a9292abc44cd28c40000c8e2f5ac7660a81c85b72af8452d7d25c070861dae91601c7803d656531650dd4e5c4100"))))

expected-test-vector-12 : Result
expected-test-vector-12 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-12 : Set
pending-test-vector-12 = Pending (evalRaw test-test-vector-12 ≡ expected-test-vector-12)
```

## test-vector-13

```
-- builtin/semantics/verifyEd25519Signature/test-vector-13
test-test-vector-13 : Untyped
test-test-vector-13 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "6fe83693d011d111131c4f3fbaaa40a9d3d76b30012ff73bb0e39ec27ab18257")))) (UCon (tagCon bytestring (mkByteString "5a8d9d0a22357e6655f9c785")))) (UCon (tagCon bytestring (mkByteString "0f9ad9793033a2fa06614b277d37381e6d94f65ac2a5a94558d09ed6ce922258c1a567952e863ac94297aec3c0d0c8ddf71084e504860bb6ba27449b55adc40e"))))

expected-test-vector-13 : Result
expected-test-vector-13 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-13 : Set
pending-test-vector-13 = Pending (evalRaw test-test-vector-13 ≡ expected-test-vector-13)
```

## test-vector-14

```
-- builtin/semantics/verifyEd25519Signature/test-vector-14
test-test-vector-14 : Untyped
test-test-vector-14 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "a2eb8c0501e30bae0cf842d2bde8dec7386f6b7fc3981b8c57c9792bb94cf2dd")))) (UCon (tagCon bytestring (mkByteString "b87d3813e03f58cf19fd0b6395")))) (UCon (tagCon bytestring (mkByteString "d8bb64aad8c9955a115a793addd24f7f2b077648714f49c4694ec995b330d09d640df310f447fd7b6cb5c14f9fe9f490bcf8cfadbfd2169c8ac20d3b8af49a0c"))))

expected-test-vector-14 : Result
expected-test-vector-14 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-14 : Set
pending-test-vector-14 = Pending (evalRaw test-test-vector-14 ≡ expected-test-vector-14)
```

## test-vector-15

```
-- builtin/semantics/verifyEd25519Signature/test-vector-15
test-test-vector-15 : Untyped
test-test-vector-15 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "cf3af898467a5b7a52d33d53bc037e2642a8da996903fc252217e9c033e2f291")))) (UCon (tagCon bytestring (mkByteString "55c7fa434f5ed8cdec2b7aeac173")))) (UCon (tagCon bytestring (mkByteString "6ee3fe81e23c60eb2312b2006b3b25e6838e02106623f844c44edb8dafd66ab0671087fd195df5b8f58a1d6e52af42908053d55c7321010092748795ef94cf06"))))

expected-test-vector-15 : Result
expected-test-vector-15 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-15 : Set
pending-test-vector-15 = Pending (evalRaw test-test-vector-15 ≡ expected-test-vector-15)
```

## test-vector-16

```
-- builtin/semantics/verifyEd25519Signature/test-vector-16
test-test-vector-16 : Untyped
test-test-vector-16 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "fd2a565723163e29f53c9de3d5e8fbe36a7ab66e1439ec4eae9c0a604af291a5")))) (UCon (tagCon bytestring (mkByteString "0a688e79be24f866286d4646b5d81c")))) (UCon (tagCon bytestring (mkByteString "f68d04847e5b249737899c014d31c805c5007a62c0a10d50bb1538c5f35503951fbc1e08682f2cc0c92efe8f4985dec61dcbd54d4b94a22547d24451271c8b00"))))

expected-test-vector-16 : Result
expected-test-vector-16 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-16 : Set
pending-test-vector-16 = Pending (evalRaw test-test-vector-16 ≡ expected-test-vector-16)
```

## test-vector-17

```
-- builtin/semantics/verifyEd25519Signature/test-vector-17
test-test-vector-17 : Untyped
test-test-vector-17 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "34e5a8508c4743746962c066e4badea2201b8ab484de5c4f94476ccd2143955b")))) (UCon (tagCon bytestring (mkByteString "c942fa7ac6b23ab7ff612fdc8e68ef39")))) (UCon (tagCon bytestring (mkByteString "2a3d27dc40d0a8127949a3b7f908b3688f63b7f14f651aacd715940bdbe27a0809aac142f47ab0e1e44fa490ba87ce5392f33a891539caf1ef4c367cae54500c"))))

expected-test-vector-17 : Result
expected-test-vector-17 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-17 : Set
pending-test-vector-17 = Pending (evalRaw test-test-vector-17 ≡ expected-test-vector-17)
```

## test-vector-18

```
-- builtin/semantics/verifyEd25519Signature/test-vector-18
test-test-vector-18 : Untyped
test-test-vector-18 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "0445e456dacc7d5b0bbed23c8200cdb74bdcb03e4c7b73f0a2b9b46eac5d4372")))) (UCon (tagCon bytestring (mkByteString "7368724a5b0efb57d28d97622dbde725af")))) (UCon (tagCon bytestring (mkByteString "3653ccb21219202b8436fb41a32ba2618c4a133431e6e63463ceb3b6106c4d56e1d2ba165ba76eaad3dc39bffb130f1de3d8e6427db5b71938db4e272bc3e20b"))))

expected-test-vector-18 : Result
expected-test-vector-18 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-18 : Set
pending-test-vector-18 = Pending (evalRaw test-test-vector-18 ≡ expected-test-vector-18)
```

## test-vector-19

```
-- builtin/semantics/verifyEd25519Signature/test-vector-19
test-test-vector-19 : Untyped
test-test-vector-19 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "74d29127f199d86a8676aec33b4ce3f225ccb191f52c191ccd1e8cca65213a6b")))) (UCon (tagCon bytestring (mkByteString "bd8e05033f3a8bcdcbf4beceb70901c82e31")))) (UCon (tagCon bytestring (mkByteString "fbe929d743a03c17910575492f3092ee2a2bf14a60a3fcacec74a58c7334510fc262db582791322d6c8c41f1700adb80027ecabc14270b703444ae3ee7623e0a"))))

expected-test-vector-19 : Result
expected-test-vector-19 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-19 : Set
pending-test-vector-19 = Pending (evalRaw test-test-vector-19 ≡ expected-test-vector-19)
```

## test-vector-20

```
-- builtin/semantics/verifyEd25519Signature/test-vector-20
test-test-vector-20 : Untyped
test-test-vector-20 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "5b96dca497875bf9664c5e75facf3f9bc54bae913d66ca15ee85f1491ca24d2c")))) (UCon (tagCon bytestring (mkByteString "8171456f8b907189b1d779e26bc5afbb08c67a")))) (UCon (tagCon bytestring (mkByteString "73bca64e9dd0db88138eedfafcea8f5436cfb74bfb0e7733cf349baa0c49775c56d5934e1d38e36f39b7c5beb0a836510c45126f8ec4b6810519905b0ca07c09"))))

expected-test-vector-20 : Result
expected-test-vector-20 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-20 : Set
pending-test-vector-20 = Pending (evalRaw test-test-vector-20 ≡ expected-test-vector-20)
```

## test-vector-21

```
-- builtin/semantics/verifyEd25519Signature/test-vector-21
test-test-vector-21 : Untyped
test-test-vector-21 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "1ca281938529896535a7714e3584085b86ef9fec723f42819fc8dd5d8c00817f")))) (UCon (tagCon bytestring (mkByteString "8ba6a4c9a15a244a9c26bb2a59b1026f21348b49")))) (UCon (tagCon bytestring (mkByteString "a1adc2bc6a2d980662677e7fdff6424de7dba50f5795ca90fdf3e96e256f3285cac71d3360482e993d0294ba4ec7440c61affdf35fe83e6e04263937db93f105"))))

expected-test-vector-21 : Result
expected-test-vector-21 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-21 : Set
pending-test-vector-21 = Pending (evalRaw test-test-vector-21 ≡ expected-test-vector-21)
```

## test-vector-22

```
-- builtin/semantics/verifyEd25519Signature/test-vector-22
test-test-vector-22 : Untyped
test-test-vector-22 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "7fae45dd0a05971026d410bc497af5be7d0827a82a145c203f625dfcb8b03ba8")))) (UCon (tagCon bytestring (mkByteString "1d566a6232bbaab3e6d8804bb518a498ed0f904986")))) (UCon (tagCon bytestring (mkByteString "bb61cf84de61862207c6a455258bc4db4e15eea0317ff88718b882a06b5cf6ec6fd20c5a269e5d5c805bafbcc579e2590af414c7c227273c102a10070cdfe80f"))))

expected-test-vector-22 : Result
expected-test-vector-22 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-22 : Set
pending-test-vector-22 = Pending (evalRaw test-test-vector-22 ≡ expected-test-vector-22)
```

## test-vector-23

```
-- builtin/semantics/verifyEd25519Signature/test-vector-23
test-test-vector-23 : Untyped
test-test-vector-23 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "48359b850d23f0715d94bb8bb75e7e14322eaf14f06f28a805403fbda002fc85")))) (UCon (tagCon bytestring (mkByteString "1b0afb0ac4ba9ab7b7172cddc9eb42bba1a64bce47d4")))) (UCon (tagCon bytestring (mkByteString "b6dcd09989dfbac54322a3ce87876e1d62134da998c79d24b50bd7a6a797d86a0e14dc9d7491d6c14a673c652cfbec9f962a38c945da3b2f0879d0b68a921300"))))

expected-test-vector-23 : Result
expected-test-vector-23 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-23 : Set
pending-test-vector-23 = Pending (evalRaw test-test-vector-23 ≡ expected-test-vector-23)
```

## test-vector-24

```
-- builtin/semantics/verifyEd25519Signature/test-vector-24
test-test-vector-24 : Untyped
test-test-vector-24 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "fdb30673402faf1c8033714f3517e47cc0f91fe70cf3836d6c23636e3fd2287c")))) (UCon (tagCon bytestring (mkByteString "507c94c8820d2a5793cbf3442b3d71936f35fe3afef316")))) (UCon (tagCon bytestring (mkByteString "7ef66e5e86f2360848e0014e94880ae2920ad8a3185a46b35d1e07dea8fa8ae4f6b843ba174d99fa7986654a0891c12a794455669375bf92af4cc2770b579e0c"))))

expected-test-vector-24 : Result
expected-test-vector-24 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-24 : Set
pending-test-vector-24 = Pending (evalRaw test-test-vector-24 ≡ expected-test-vector-24)
```

## test-vector-25

```
-- builtin/semantics/verifyEd25519Signature/test-vector-25
test-test-vector-25 : Untyped
test-test-vector-25 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "b1d39801892027d58a8c64335163195893bfc1b61dbeca3260497e1f30371107")))) (UCon (tagCon bytestring (mkByteString "d3d615a8472d9962bb70c5b5466a3d983a4811046e2a0ef5")))) (UCon (tagCon bytestring (mkByteString "836afa764d9c48aa4770a4388b654e97b3c16f082967febca27f2fc47ddfd9244b03cfc729698acf5109704346b60b230f255430089ddc56912399d1122de70a"))))

expected-test-vector-25 : Result
expected-test-vector-25 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-25 : Set
pending-test-vector-25 = Pending (evalRaw test-test-vector-25 ≡ expected-test-vector-25)
```

## test-vector-26

```
-- builtin/semantics/verifyEd25519Signature/test-vector-26
test-test-vector-26 : Untyped
test-test-vector-26 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "d0c846f97fe28585c0ee159015d64c56311c886eddcc185d296dbb165d2625d6")))) (UCon (tagCon bytestring (mkByteString "6ada80b6fa84f7034920789e8536b82d5e4678059aed27f71c")))) (UCon (tagCon bytestring (mkByteString "16e462a29a6dd498685a3718b3eed00cc1598601ee47820486032d6b9acc9bf89f57684e08d8c0f05589cda2882a05dc4c63f9d0431d6552710812433003bc08"))))

expected-test-vector-26 : Result
expected-test-vector-26 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-26 : Set
pending-test-vector-26 = Pending (evalRaw test-test-vector-26 ≡ expected-test-vector-26)
```

## test-vector-27

```
-- builtin/semantics/verifyEd25519Signature/test-vector-27
test-test-vector-27 : Untyped
test-test-vector-27 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "2bf32ba142ba4622d8f3e29ecd85eea07b9c47be9d64412c9b510b27dd218b23")))) (UCon (tagCon bytestring (mkByteString "82cb53c4d5a013bae5070759ec06c3c6955ab7a4050958ec328c")))) (UCon (tagCon bytestring (mkByteString "881f5b8c5a030df0f75b6634b070dd27bd1ee3c08738ae349338b3ee6469bbf9760b13578a237d5182535ede121283027a90b5f865d63a6537dca07b44049a0f"))))

expected-test-vector-27 : Result
expected-test-vector-27 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-27 : Set
pending-test-vector-27 = Pending (evalRaw test-test-vector-27 ≡ expected-test-vector-27)
```

## test-vector-28

```
-- builtin/semantics/verifyEd25519Signature/test-vector-28
test-test-vector-28 : Untyped
test-test-vector-28 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "94d23d977c33e49e5e4992c68f25ec99a27c41ce6b91f2bfa0cd8292fe962835")))) (UCon (tagCon bytestring (mkByteString "a9a8cbb0ad585124e522abbfb40533bdd6f49347b55b18e8558cb0")))) (UCon (tagCon bytestring (mkByteString "3acd39bec8c3cd2b44299722b5850a0400c1443590fd4861d59aae7496acb3df73fc3fdf7969ae5f50ba47dddc435246e5fd376f6b891cd4c2caf5d614b6170c"))))

expected-test-vector-28 : Result
expected-test-vector-28 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-28 : Set
pending-test-vector-28 = Pending (evalRaw test-test-vector-28 ≡ expected-test-vector-28)
```

## test-vector-29

```
-- builtin/semantics/verifyEd25519Signature/test-vector-29
test-test-vector-29 : Untyped
test-test-vector-29 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "9d084aa8b97a6b9bafa496dbc6f76f3306a116c9d917e681520a0f914369427e")))) (UCon (tagCon bytestring (mkByteString "5cb6f9aa59b80eca14f6a68fb40cf07b794e75171fba96262c1c6adc")))) (UCon (tagCon bytestring (mkByteString "f5875423781b66216cb5e8998de5d9ffc29d1d67107054ace3374503a9c3ef811577f269de81296744bd706f1ac478caf09b54cdf871b3f802bd57f9a6cb9101"))))

expected-test-vector-29 : Result
expected-test-vector-29 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-29 : Set
pending-test-vector-29 = Pending (evalRaw test-test-vector-29 ≡ expected-test-vector-29)
```

## test-vector-30

```
-- builtin/semantics/verifyEd25519Signature/test-vector-30
test-test-vector-30 : Untyped
test-test-vector-30 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "16cee8a3f2631834c88b670897ff0b08ce90cc147b4593b3f1f403727f7e7ad5")))) (UCon (tagCon bytestring (mkByteString "32fe27994124202153b5c70d3813fdee9c2aa6e7dc743d4d535f1840a5")))) (UCon (tagCon bytestring (mkByteString "d834197c1a3080614e0a5fa0aaaa808824f21c38d692e6ffbd200f7dfb3c8f44402a7382180b98ad0afc8eec1a02acecf3cb7fde627b9f18111f260ab1db9a07"))))

expected-test-vector-30 : Result
expected-test-vector-30 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-30 : Set
pending-test-vector-30 = Pending (evalRaw test-test-vector-30 ≡ expected-test-vector-30)
```

## test-vector-31

```
-- builtin/semantics/verifyEd25519Signature/test-vector-31
test-test-vector-31 : Untyped
test-test-vector-31 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "23be323c562dfd71ce65f5bba56a74a3a6dfc36b573d2f94f635c7f9b4fd5a5b")))) (UCon (tagCon bytestring (mkByteString "bb3172795710fe00054d3b5dfef8a11623582da68bf8e46d72d27cece2aa")))) (UCon (tagCon bytestring (mkByteString "0f8fad1e6bde771b4f5420eac75c378bae6db5ac6650cd2bc210c1823b432b48e016b10595458ffab92f7a8989b293ceb8dfed6c243a2038fc06652aaaf16f02"))))

expected-test-vector-31 : Result
expected-test-vector-31 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `verifyEd25519Signature`.
pending-test-vector-31 : Set
pending-test-vector-31 = Pending (evalRaw test-test-vector-31 ≡ expected-test-vector-31)
```
