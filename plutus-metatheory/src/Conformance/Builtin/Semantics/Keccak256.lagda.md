---
title: Conformance.Builtin.Semantics.Keccak256
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/keccak_256`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Keccak256 where

open import Conformance.Eval
```

## keccak_256-empty

```
-- builtin/semantics/keccak_256/keccak_256-empty
-- Test vector (0-bit input) from ShortMsgKAT_256.txt in
-- https://keccak.team/obsolete/KeccakKAT-3.zip.  The Keccak function we're
-- testing here is the version used by Ethereum, which was the Keccak submission
-- in round 3 of the SHA-3 competition.  The final SHA-3 hash function is a
-- modified version of that.
test-keccak-256-empty : Untyped
test-keccak-256-empty = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin keccak-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"))))

expected-keccak-256-empty : Result
expected-keccak-256-empty = success (UCon (tagCon bool true))

-- Pending: postulated builtin `keccak-256`.
pending-keccak-256-empty : Set
pending-keccak-256-empty = Pending (evalRaw test-keccak-256-empty ≡ expected-keccak-256-empty)
```

## keccak_256-length-200

```
-- builtin/semantics/keccak_256/keccak_256-length-200
-- Test vector (200-bit input) from ShortMsgKAT_256.txt in
-- https://keccak.team/obsolete/KeccakKAT-3.zip.  The Keccak function we're
-- testing here is the version used by Ethereum, which was the Keccak submission
-- in round 3 of the SHA-3 competition.  The final SHA-3 hash function is a
-- modified version of that.
test-keccak-256-length-200 : Untyped
test-keccak-256-length-200 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin keccak-256) (UCon (tagCon bytestring (mkByteString "aafdc9243d3d4a096558a360cc27c8d862f0be73db5e88aa55"))))) (UCon (tagCon bytestring (mkByteString "6fffa070b865be3ee766dc2db49b6aa55c369f7de3703ada2612d754145c01e6"))))

expected-keccak-256-length-200 : Result
expected-keccak-256-length-200 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `keccak-256`.
pending-keccak-256-length-200 : Set
pending-keccak-256-length-200 = Pending (evalRaw test-keccak-256-length-200 ≡ expected-keccak-256-length-200)
```
