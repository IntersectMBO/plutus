---
title: Conformance.Builtin.Semantics.Bls12381G2Compress
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G2_compress`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G2Compress where

open import Conformance.Eval
```

## compress

```
-- builtin/semantics/bls12_381_G2_compress/compress
-- Check that compression of a random point in G2 succeeds and gives the expected result.
test-compress : Untyped
test-compress = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))

expected-compress : Result
expected-compress = success (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-uncompress`.
pending-compress : Set
pending-compress = Pending (evalRaw test-compress ≡ expected-compress)
```
