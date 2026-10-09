---
title: Conformance.Builtin.Parser.Unit
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/parser/unit`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Parser.Unit where

open import Conformance.Eval
```

## unit

```
-- builtin/parser/unit/unit
test-unit : Untyped
test-unit = (UCon (tagCon unit tt))

expected-unit : Result
expected-unit = success (UCon (tagCon unit tt))

_ : evalRaw test-unit ≡ expected-unit
_ = refl
```

## unit-fail-1

Skipped: the program does not parse or has free variables (`parse/decode error`).

## unit-fail-2

Skipped: the program does not parse or has free variables (`parse/decode error`).
