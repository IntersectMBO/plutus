---
title: Conformance.Builtin.Parser.List
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/parser/list`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Parser.List where

open import Conformance.Eval
```

## emptyList

```
-- builtin/parser/list/emptyList
test-emptyList : Untyped
test-emptyList = (UCon (tagCon (list integer) ([])))

expected-emptyList : Result
expected-emptyList = success (UCon (tagCon (list integer) ([])))

_ : evalRaw test-emptyList ≡ expected-emptyList
_ = refl
```

## illTypedList-01

Skipped: the program does not parse or has free variables (`parse/decode error`).

## illTypedList-02

Skipped: the program does not parse or has free variables (`parse/decode error`).

## simpleList

Skipped: the program does not parse or has free variables (`parse/decode error`).

## unitList

Skipped: the program does not parse or has free variables (`parse/decode error`).
