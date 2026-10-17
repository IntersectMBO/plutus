---
title: Conformance.Builtin.Semantics.Ripemd160
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/ripemd_160`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Ripemd160 where

open import Conformance.Eval
```

## ripemd_160-empty

```
-- builtin/semantics/ripemd_160/ripemd_160-empty
-- Test vector (0-bit input) for Ripemd_160.
-- Output obtained using the online tool https://emn178.github.io/online-tools/ripemd_160.html
test-ripemd-160-empty : Untyped
test-ripemd-160-empty = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin ripemd-160) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\156\DC1\133\165\197\233\252Ta(\b\151~\232\245H\178%\141\&1"))))

expected-ripemd-160-empty : Result
expected-ripemd-160-empty = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `ripemd-160`.
pending-ripemd-160-empty : Set
pending-ripemd-160-empty = Pending (evalRaw test-ripemd-160-empty ≡ expected-ripemd-160-empty)
```

## ripemd_160-length-200

```
-- builtin/semantics/ripemd_160/ripemd_160-length-200
-- Test vector (0-bit input) for Ripemd_160.
-- Output obtained using the online tool https://emn178.github.io/online-tools/ripemd_160.html
test-ripemd-160-length-200 : Untyped
test-ripemd-160-length-200 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin ripemd-160) (UCon (tagCon bytestring (mkByteString ".~\168M\164\188M|\251F>?,\134G\ENQz\255\243\251\236\236\161\210\NUL"))))) (UCon (tagCon bytestring (mkByteString "\241\137!\DC1Sp\176I\233\157\253\212\159\201+7\GS\215\199\233"))))

expected-ripemd-160-length-200 : Result
expected-ripemd-160-length-200 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `ripemd-160`.
pending-ripemd-160-length-200 : Set
pending-ripemd-160-length-200 = Pending (evalRaw test-ripemd-160-length-200 ≡ expected-ripemd-160-length-200)
```
