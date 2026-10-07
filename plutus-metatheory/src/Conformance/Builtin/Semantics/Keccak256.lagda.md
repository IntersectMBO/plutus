---
title: Conformance.Builtin.Semantics.Keccak256
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

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
test-keccak-256-empty = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin keccak-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\197\210F\SOH\134\247#<\146~}\178\220\199\ETX\192\229\NUL\182S\202\130';{\250\216\EOT]\133\164p"))))

expected-keccak-256-empty : Result
expected-keccak-256-empty = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `keccak-256`.
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
test-keccak-256-length-200 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin keccak-256) (UCon (tagCon bytestring (mkByteString "\170\253\201$==J\teX\163`\204'\200\216b\240\190s\219^\136\170U"))))) (UCon (tagCon bytestring (mkByteString "o\255\160p\184e\190>\231f\220-\180\155j\165\\6\159}\227p:\218&\DC2\215T\DC4\\\SOH\230"))))

expected-keccak-256-length-200 : Result
expected-keccak-256-length-200 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `keccak-256`.
pending-keccak-256-length-200 : Set
pending-keccak-256-length-200 = Pending (evalRaw test-keccak-256-length-200 ≡ expected-keccak-256-length-200)
```
