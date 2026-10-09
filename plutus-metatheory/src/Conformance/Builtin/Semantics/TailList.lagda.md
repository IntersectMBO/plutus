---
title: Conformance.Builtin.Semantics.TailList
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/tailList`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.TailList where

open import Conformance.Eval
```

## tailList-01

```
-- builtin/semantics/tailList/tailList-01
test-tailList-01 : Untyped
test-tailList-01 = (UApp (UForce (UBuiltin tailList)) (UCon (tagCon (list integer) ([]))))

expected-tailList-01 : Result
expected-tailList-01 = failure

_ : evalRaw test-tailList-01 ≡ expected-tailList-01
_ = refl
```

## tailList-partial

```
-- builtin/semantics/tailList/tailList-partial
-- tail is partial like haskell's and blows up when given an empty list
test-tailList-partial : Untyped
test-tailList-partial = (UApp (UForce (UBuiltin tailList)) (UApp (UBuiltin mkNilData) (UCon (tagCon unit tt))))

expected-tailList-partial : Result
expected-tailList-partial = failure

_ : evalRaw test-tailList-partial ≡ expected-tailList-partial
_ = refl
```
