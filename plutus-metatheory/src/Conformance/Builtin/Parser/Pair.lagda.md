---
title: Conformance.Builtin.Parser.Pair
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/parser/pair`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Parser.Pair where

open import Conformance.Eval
```

## illTypedNestedPair

Skipped: the program does not parse or has free variables (`parse/decode error`).

## illTypedPair-01

Skipped: the program does not parse or has free variables (`parse/decode error`).

## illTypedPair-02

Skipped: the program does not parse or has free variables (`parse/decode error`).

## nestedPair

```
-- builtin/parser/pair/nestedPair
test-nestedPair : Untyped
test-nestedPair = (UCon (tagCon (pair integer (pair unit bool)) ((ℤ.pos 12345) , (tt , true))))

expected-nestedPair : Result
expected-nestedPair = success (UCon (tagCon (pair integer (pair unit bool)) ((ℤ.pos 12345) , (tt , true))))

_ : evalRaw test-nestedPair ≡ expected-nestedPair
_ = refl
```

## simplePair

```
-- builtin/parser/pair/simplePair
test-simplePair : Untyped
test-simplePair = (UCon (tagCon (pair integer bool) ((ℤ.pos 12345) , true)))

expected-simplePair : Result
expected-simplePair = success (UCon (tagCon (pair integer bool) ((ℤ.pos 12345) , true)))

_ : evalRaw test-simplePair ≡ expected-simplePair
_ = refl
```
