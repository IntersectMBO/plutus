---
title: Conformance.Builtin.Semantics.MkCons
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/mkCons`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.MkCons where

open import Conformance.Eval
```

## divideInteger

```
-- builtin/semantics/mkCons/divideInteger
test-divideInteger : Untyped
test-divideInteger = (UApp (UApp (UBuiltin divideInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 0))))

expected-divideInteger : Result
expected-divideInteger = failure

_ : evalRaw test-divideInteger ≡ expected-divideInteger
_ = refl
```

## mkCons-01

```
-- builtin/semantics/mkCons/mkCons-01
test-mkCons-01 : Untyped
test-mkCons-01 = (UApp (UApp (UForce (UBuiltin mkCons)) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon (list integer) ([]))))

expected-mkCons-01 : Result
expected-mkCons-01 = success (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ [])))

_ : evalRaw test-mkCons-01 ≡ expected-mkCons-01
_ = refl
```

## mkCons-02

```
-- builtin/semantics/mkCons/mkCons-02
test-mkCons-02 : Untyped
test-mkCons-02 = (UApp (UApp (UForce (UBuiltin mkCons)) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ []))))

expected-mkCons-02 : Result
expected-mkCons-02 = success (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.pos 1) ∷ (ℤ.pos 2) ∷ [])))

_ : evalRaw test-mkCons-02 ≡ expected-mkCons-02
_ = refl
```

## mkCons-fail

```
-- builtin/semantics/mkCons/mkCons-fail
-- a type mismatch
-- plutus implementation detail: note that this conceptually should be a machine type mismatch error (unlifting error),
-- but is currently a user evaluation failure, see: https://github.com/IntersectMBO/plutus/pull/3035
test-mkCons-fail : Untyped
test-mkCons-fail = (UApp (UApp (UForce (UBuiltin mkCons)) (UCon (tagCon integer (ℤ.pos 3)))) (UApp (UBuiltin mkNilData) (UCon (tagCon unit tt))))

expected-mkCons-fail : Result
expected-mkCons-fail = failure

_ : evalRaw test-mkCons-fail ≡ expected-mkCons-fail
_ = refl
```
