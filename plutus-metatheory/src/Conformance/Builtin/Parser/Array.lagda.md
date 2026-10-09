---
title: Conformance.Builtin.Parser.Array
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/parser/array`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Parser.Array where

open import Conformance.Eval
```

## emptyArray

```
-- builtin/parser/array/emptyArray
test-emptyArray : Untyped
test-emptyArray = (UCon (tagCon (array integer) (mkArray (([])))))

expected-emptyArray : Result
expected-emptyArray = success (UCon (tagCon (array integer) (mkArray (([])))))

-- Pending: array constant.
pending-emptyArray : Set
pending-emptyArray = Pending (evalRaw test-emptyArray ≡ expected-emptyArray)
```

## illTypedArray-01

Skipped: the program does not parse or has free variables (`parse/decode error`).

## illTypedArray-02

Skipped: the program does not parse or has free variables (`parse/decode error`).

## simpleArray

```
-- builtin/parser/array/simpleArray
test-simpleArray : Untyped
test-simpleArray = (UCon (tagCon (array bool) (mkArray ((true ∷ false ∷ true ∷ [])))))

expected-simpleArray : Result
expected-simpleArray = success (UCon (tagCon (array bool) (mkArray ((true ∷ false ∷ true ∷ [])))))

-- Pending: array constant.
pending-simpleArray : Set
pending-simpleArray = Pending (evalRaw test-simpleArray ≡ expected-simpleArray)
```

## unitArray

```
-- builtin/parser/array/unitArray
test-unitArray : Untyped
test-unitArray = (UCon (tagCon (array unit) (mkArray ((tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])))))

expected-unitArray : Result
expected-unitArray = success (UCon (tagCon (array unit) (mkArray ((tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])))))

-- Pending: array constant.
pending-unitArray : Set
pending-unitArray = Pending (evalRaw test-unitArray ≡ expected-unitArray)
```
