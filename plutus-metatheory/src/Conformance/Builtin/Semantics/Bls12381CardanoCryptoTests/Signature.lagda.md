---
title: Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.Signature
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381-cardano-crypto-tests/signature`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.Signature where

open import Conformance.Eval
```

## augmented

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/signature/augmented
-- Check that a signature involving an agumentation string prepended to a message
-- is as expected.
test-augmented : Untyped
test-augmented = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "83422fd1d8f134fbbc7ad2949a0b7c38dc1f85bfd398bc58ae824ad34ace68eaa49f438872ee22e90778513a91f9685e"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UApp (UApp (UBuiltin appendByteString) (UCon (tagCon bytestring (mkByteString "52616e646f6d2076616c756520666f722074657374206175672e20")))) (UCon (tagCon bytestring (mkByteString "626c73742069732073756368206120626c617374"))))) (UCon (tagCon bytestring (mkByteString "424c535f5349475f424c53313233383147325f584d443a5348412d3235365f535357555f524f5f4e554c5f"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b756d6223a92609cccf660b6f37e6e34fbb23972fc3955710f9bb202cc84cffacd337792700ebcb4324a99c7e7c9ed6d0e1cfdce8cd879a35300957c69c524c5365f6f0a85130735f27510618bbea605a1d024bb2d3bee2a5d68a827406f11c7"))))))

expected-augmented : Result
expected-augmented = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`; postulated builtin `bls12-381-G1-hashToGroup`.
pending-augmented : Set
pending-augmented = Pending (evalRaw test-augmented ≡ expected-augmented)
```

## large-dst

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/signature/large-dst
-- Check that the procedure for using a DST greater than 255 bytes long gives the expected result.
test-large-dst : Untyped
test-large-dst = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "54657374696e67206c61726765206473742e")))) (UApp (UBuiltin sha2-256) (UApp (UApp (UBuiltin appendByteString) (UCon (tagCon bytestring (mkByteString "4832432d4f56455253495a452d4453542d")))) (UCon (tagCon bytestring (mkByteString "62f5804020e6a8e242c736d1c97bcd8262f91b88e1d70b00d10d5e315c8c6501ead0a7e367e5d394b9fcff9c15aa0f6a05e5085fdc56bcdee3865016f1c49b20e1e609a606eccabc9b9199a42345c25e06ae70028397f8fb95576f264239da3eb49629d5efeb1f1d74a3b1ac58608d893f98058f5ab870833489f5dfec52db5f92e70db05c9704cd9d644b1ae16aaafcc173d48db17e207d91308d3045b042b7241f87b8d42ac5df97d94fdf3f29d20ca2ae22c22e9c5b84b48d6daf1f7959c7c71d0169f370ebf2838479b3731885ff0d278deb632fcb83aef0ab593dddd4f5d21dac56abe08b8cb4aaf4235b1a292b91d6e8b90e39dc953c75fc460e7dd6d2bc8a372ac4efce161f5f18f861e67e5717c86805a05cc53ff493e91de2b85d3166b353f5bbc64bae0d2a4787"))))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "a16b5778b5b88519b6caf05921d0d9b8b94a33d1daaa0c7fbfa66d52e801a5e798fae840bb9608aa31712e0b1b3a054a")))))

expected-large-dst : Result
expected-large-dst = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-hashToGroup`; postulated builtin `sha2-256`; postulated builtin `bls12-381-G1-uncompress`.
pending-large-dst : Set
pending-large-dst = Pending (evalRaw test-large-dst ≡ expected-large-dst)
```
