---
title: Conformance.Builtin.Semantics.Bls12381G1Compress
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

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
test-compress = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245")))))

expected-compress : Result
expected-compress = success (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-uncompress`.
pending-compress : Set
pending-compress = Pending (evalRaw test-compress ≡ expected-compress)
```
