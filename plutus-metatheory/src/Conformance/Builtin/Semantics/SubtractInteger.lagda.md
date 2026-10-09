---
title: Conformance.Builtin.Semantics.SubtractInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/subtractInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.SubtractInteger where

open import Conformance.Eval
```

## subtractInteger-01

```
-- builtin/semantics/subtractInteger/subtractInteger-01
test-subtractInteger-01 : Untyped
test-subtractInteger-01 = (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1))))

expected-subtractInteger-01 : Result
expected-subtractInteger-01 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-subtractInteger-01 ≡ expected-subtractInteger-01
_ = refl
```

## subtractInteger-02

```
-- builtin/semantics/subtractInteger/subtractInteger-02
test-subtractInteger-02 : Untyped
test-subtractInteger-02 = (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 123423)))) (UCon (tagCon integer (ℤ.negsuc 794378954789297840))))

expected-subtractInteger-02 : Result
expected-subtractInteger-02 = success (UCon (tagCon integer (ℤ.pos 794378954789421264)))

_ : evalRaw test-subtractInteger-02 ≡ expected-subtractInteger-02
_ = refl
```

## subtractInteger-03

```
-- builtin/semantics/subtractInteger/subtractInteger-03
test-subtractInteger-03 : Untyped
test-subtractInteger-03 = (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 134782734132417234781342718231486243)))) (UCon (tagCon integer (ℤ.pos 23443231))))

expected-subtractInteger-03 : Result
expected-subtractInteger-03 = success (UCon (tagCon integer (ℤ.pos 134782734132417234781342718208043012)))

_ : evalRaw test-subtractInteger-03 ≡ expected-subtractInteger-03
_ = refl
```

## subtractInteger-04

```
-- builtin/semantics/subtractInteger/subtractInteger-04
test-subtractInteger-04 : Untyped
test-subtractInteger-04 = (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.negsuc 327893248793249782347890))))

expected-subtractInteger-04 : Result
expected-subtractInteger-04 = success (UCon (tagCon integer (ℤ.pos 327893248793249782347891)))

_ : evalRaw test-subtractInteger-04 ≡ expected-subtractInteger-04
_ = refl
```
