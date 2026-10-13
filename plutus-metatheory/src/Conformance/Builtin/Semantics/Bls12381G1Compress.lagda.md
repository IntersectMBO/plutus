---
title: Conformance.Builtin.Semantics.Bls12381G1Compress
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G1_compress`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G1Compress where

open import Conformance.Eval
```

## compress

```
-- builtin/semantics/bls12_381_G1_compress/compress
-- Check that compression of a random point in G1 succeeds and gives the expected result.
test-compress : Untyped
test-compress = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5")))))

expected-compress : Result
expected-compress = success (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-uncompress`.
pending-compress : Set
pending-compress = Pending (evalRaw test-compress ≡ expected-compress)
```
