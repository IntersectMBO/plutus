---
title: Conformance.Builtin.Semantics.Bls12381G2Compress
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

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
test-compress = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241")))))

expected-compress : Result
expected-compress = success (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-uncompress`.
pending-compress : Set
pending-compress = Pending (evalRaw test-compress ≡ expected-compress)
```
