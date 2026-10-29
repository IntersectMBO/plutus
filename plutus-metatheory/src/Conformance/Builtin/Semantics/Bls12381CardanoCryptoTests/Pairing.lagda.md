---
title: Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.Pairing
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381-cardano-crypto-tests/pairing`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.Pairing where

open import Conformance.Eval
```

## balanced

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/balanced
-- <[a]P,Q> = <P,[a]Q>
test-balanced : Untyped
test-balanced = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "8baa4f3fcd895033f93494b040ccd7dfb77cb759cd2e150bfff4264873174509cd22230423b70896b17c8fc3660f6b21"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b67029fbf3ab8e62ab6b499f541537fc07d9466e668392df2bc19762d7dc48b64be09a448cd46dbfe21819a91cd0ab3205f1316ad1cc32853f3f1a1d06497f5cfbc2d753dfc01bff177adeb93f24d452045435dc6eb29f5610b66cd0dd3fb352")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "840463aa2f2cda89985b1f3f5eb43b9c29809765d2747d60734b19d6f90610effdfc500af7d458a3e78cee0945ddc669"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a80f311db6f2fdc45404870f4c55b65a9a59a35efcfa2a7c595f3955226076bbaa33e403c0d4749495d9423b806f9dbe08cca770e08fa535daefb6dba2edb62f8b9aff6bae83bf48819bcdf98f07e79de8635e8521ddecae19b01a6777bc4684"))))))

expected-balanced : Result
expected-balanced = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-balanced : Set
pending-balanced = Pending (evalRaw test-balanced ≡ expected-balanced)
```

## left-additive

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/left-additive
-- <[a]P,Q><[b]P,Q> = <[a+b]P,Q>
test-left-additive : Untyped
test-left-additive = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-mulMlResult) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "8baa4f3fcd895033f93494b040ccd7dfb77cb759cd2e150bfff4264873174509cd22230423b70896b17c8fc3660f6b21"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b67029fbf3ab8e62ab6b499f541537fc07d9466e668392df2bc19762d7dc48b64be09a448cd46dbfe21819a91cd0ab3205f1316ad1cc32853f3f1a1d06497f5cfbc2d753dfc01bff177adeb93f24d452045435dc6eb29f5610b66cd0dd3fb352")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "a4a925cb9c0580c14cbc8ec54447eb20070336a61c349c6a64b0d87e4db89d77734021cd88e2da369bdd85c0518c66c4"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b67029fbf3ab8e62ab6b499f541537fc07d9466e668392df2bc19762d7dc48b64be09a448cd46dbfe21819a91cd0ab3205f1316ad1cc32853f3f1a1d06497f5cfbc2d753dfc01bff177adeb93f24d452045435dc6eb29f5610b66cd0dd3fb352"))))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "aecf54083187026a6b689e70af54375ab7cc6d0d311acb6203730a2904654d6e92f82e62006c0d5e21094155eb93cc98"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b67029fbf3ab8e62ab6b499f541537fc07d9466e668392df2bc19762d7dc48b64be09a448cd46dbfe21819a91cd0ab3205f1316ad1cc32853f3f1a1d06497f5cfbc2d753dfc01bff177adeb93f24d452045435dc6eb29f5610b66cd0dd3fb352"))))))

expected-left-additive : Result
expected-left-additive = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-mulMlResult`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-left-additive : Set
pending-left-additive = Pending (evalRaw test-left-additive ≡ expected-left-additive)
```

## left-multiplicative

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/left-multiplicative
-- <[a]P,[b]Q> = <[ab]P,Q>
test-left-multiplicative : Untyped
test-left-multiplicative = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "8baa4f3fcd895033f93494b040ccd7dfb77cb759cd2e150bfff4264873174509cd22230423b70896b17c8fc3660f6b21"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "9906a15ff959b496f478dd17348b32c033236db5a7437768a30c5ce87d9b6adfa7bf2223a0721c93a92f33abac9b2faf00d25e48b0f3cc52595264ef9ad0aa7b81e20b3c8634d577883ff5fc2373a021a1e57826f420a74f3ce0fbd2dcf79415")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "b2bb2433441c452b78f5be911aa136dd2c886a9ac329cb6c805e50d5255891fcc389b1190432f16a109c6f431f0f8023"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b67029fbf3ab8e62ab6b499f541537fc07d9466e668392df2bc19762d7dc48b64be09a448cd46dbfe21819a91cd0ab3205f1316ad1cc32853f3f1a1d06497f5cfbc2d753dfc01bff177adeb93f24d452045435dc6eb29f5610b66cd0dd3fb352"))))))

expected-left-multiplicative : Result
expected-left-multiplicative = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-left-multiplicative : Set
pending-left-multiplicative = Pending (evalRaw test-left-multiplicative ≡ expected-left-multiplicative)
```

## right-additive

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/right-additive
-- <P,[a]Q><P,[b]Q> = <P,[a+b]Q>
test-right-additive : Untyped
test-right-additive = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-mulMlResult) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "840463aa2f2cda89985b1f3f5eb43b9c29809765d2747d60734b19d6f90610effdfc500af7d458a3e78cee0945ddc669"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a80f311db6f2fdc45404870f4c55b65a9a59a35efcfa2a7c595f3955226076bbaa33e403c0d4749495d9423b806f9dbe08cca770e08fa535daefb6dba2edb62f8b9aff6bae83bf48819bcdf98f07e79de8635e8521ddecae19b01a6777bc4684")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "840463aa2f2cda89985b1f3f5eb43b9c29809765d2747d60734b19d6f90610effdfc500af7d458a3e78cee0945ddc669"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "9906a15ff959b496f478dd17348b32c033236db5a7437768a30c5ce87d9b6adfa7bf2223a0721c93a92f33abac9b2faf00d25e48b0f3cc52595264ef9ad0aa7b81e20b3c8634d577883ff5fc2373a021a1e57826f420a74f3ce0fbd2dcf79415"))))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "840463aa2f2cda89985b1f3f5eb43b9c29809765d2747d60734b19d6f90610effdfc500af7d458a3e78cee0945ddc669"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a63be4a1a776cadc7fc2e2d823bcc905f8f9cb0ebe662360d28d9964b022a99ce34a48b2e93cfceebc9bc1d79a3338da03a41393717239e66d4db06a87510b99fe04b0840c87c4051030b25e56ba34248d9ed30c82e8e501a616097299eefd62"))))))

expected-right-additive : Result
expected-right-additive = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-mulMlResult`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-right-additive : Set
pending-right-additive = Pending (evalRaw test-right-additive ≡ expected-right-additive)
```

## right-multiplicative

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/right-multiplicative
-- <[a]P,[b]Q> = <P,[ab]Q>
test-right-multiplicative : Untyped
test-right-multiplicative = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "8baa4f3fcd895033f93494b040ccd7dfb77cb759cd2e150bfff4264873174509cd22230423b70896b17c8fc3660f6b21"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "9906a15ff959b496f478dd17348b32c033236db5a7437768a30c5ce87d9b6adfa7bf2223a0721c93a92f33abac9b2faf00d25e48b0f3cc52595264ef9ad0aa7b81e20b3c8634d577883ff5fc2373a021a1e57826f420a74f3ce0fbd2dcf79415")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "840463aa2f2cda89985b1f3f5eb43b9c29809765d2747d60734b19d6f90610effdfc500af7d458a3e78cee0945ddc669"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "82606f4c771ca685bfc1bb9c51c886d0daa0f63fbb0f6a24b512a1b9b92d401e556cbffdc204c0a85192c865ed73f8090da58ecd1690d5a3b236cc5d40a98988f9602a6d114edb59954ef4e21692f2d48219aeacb964604849336059ceece69f"))))))

expected-right-multiplicative : Result
expected-right-multiplicative = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-right-multiplicative : Set
pending-right-multiplicative = Pending (evalRaw test-right-multiplicative ≡ expected-right-multiplicative)
```

## swap-scalars

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/swap-scalars
-- <[a]P,[b]Q> = <[b]P,[a]Q>
test-swap-scalars : Untyped
test-swap-scalars = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "8baa4f3fcd895033f93494b040ccd7dfb77cb759cd2e150bfff4264873174509cd22230423b70896b17c8fc3660f6b21"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "9906a15ff959b496f478dd17348b32c033236db5a7437768a30c5ce87d9b6adfa7bf2223a0721c93a92f33abac9b2faf00d25e48b0f3cc52595264ef9ad0aa7b81e20b3c8634d577883ff5fc2373a021a1e57826f420a74f3ce0fbd2dcf79415")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "a4a925cb9c0580c14cbc8ec54447eb20070336a61c349c6a64b0d87e4db89d77734021cd88e2da369bdd85c0518c66c4"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a80f311db6f2fdc45404870f4c55b65a9a59a35efcfa2a7c595f3955226076bbaa33e403c0d4749495d9423b806f9dbe08cca770e08fa535daefb6dba2edb62f8b9aff6bae83bf48819bcdf98f07e79de8635e8521ddecae19b01a6777bc4684"))))))

expected-swap-scalars : Result
expected-swap-scalars = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-swap-scalars : Set
pending-swap-scalars = Pending (evalRaw test-swap-scalars ≡ expected-swap-scalars)
```
