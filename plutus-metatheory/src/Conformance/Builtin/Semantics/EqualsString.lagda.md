---
title: Conformance.Builtin.Semantics.EqualsString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/equalsString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.EqualsString where

open import Conformance.Eval
```

## equalsString-01

```
-- builtin/semantics/equalsString/equalsString-01
test-equalsString-01 : Untyped
test-equalsString-01 = (UApp (UApp (UBuiltin equalsString) (UCon (tagCon string "Ola"))) (UCon (tagCon string " mundo!")))

expected-equalsString-01 : Result
expected-equalsString-01 = success (UCon (tagCon bool false))

_ : evalRaw test-equalsString-01 ≡ expected-equalsString-01
_ = refl
```

## equalsString-02

```
-- builtin/semantics/equalsString/equalsString-02
test-equalsString-02 : Untyped
test-equalsString-02 = (UApp (UApp (UBuiltin equalsString) (UCon (tagCon string "Ola"))) (UCon (tagCon string "Ola")))

expected-equalsString-02 : Result
expected-equalsString-02 = success (UCon (tagCon bool true))

_ : evalRaw test-equalsString-02 ≡ expected-equalsString-02
_ = refl
```
