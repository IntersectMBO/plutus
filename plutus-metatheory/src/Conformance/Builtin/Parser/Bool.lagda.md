---
title: Conformance.Builtin.Parser.Bool
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/parser/bool`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Parser.Bool where

open import Conformance.Eval
```

## False

```
-- builtin/parser/bool/False
test-False : Untyped
test-False = (UCon (tagCon bool false))

expected-False : Result
expected-False = success (UCon (tagCon bool false))

_ : evalRaw test-False ≡ expected-False
_ = refl
```

## Maybe

Skipped: the program does not parse (`parse/decode error`).

## True

```
-- builtin/parser/bool/True
test-True : Untyped
test-True = (UCon (tagCon bool true))

expected-True : Result
expected-True = success (UCon (tagCon bool true))

_ : evalRaw test-True ≡ expected-True
_ = refl
```

## boolean

Skipped: the program does not parse (`parse/decode error`).

## false-lc

Skipped: the program does not parse (`parse/decode error`).

## true-lc

Skipped: the program does not parse (`parse/decode error`).
