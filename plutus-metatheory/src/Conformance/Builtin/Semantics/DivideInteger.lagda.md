---
title: Conformance.Builtin.Semantics.DivideInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/divideInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.DivideInteger where

open import Conformance.Eval
```

## divideInteger-01

```
-- builtin/semantics/divideInteger/divideInteger-01
test-divideInteger-01 : Untyped
test-divideInteger-01 = (UApp (UApp (UBuiltin divideInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))

expected-divideInteger-01 : Result
expected-divideInteger-01 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-divideInteger-01 ≡ expected-divideInteger-01
_ = refl
```

## divideInteger-neg-neg

```
-- builtin/semantics/divideInteger/divideInteger-neg-neg
test-divideInteger-neg-neg : Untyped
test-divideInteger-neg-neg = (UApp (UApp (UBuiltin divideInteger) (UCon (tagCon integer (ℤ.negsuc 502)))) (UCon (tagCon integer (ℤ.negsuc 1777777776))))

expected-divideInteger-neg-neg : Result
expected-divideInteger-neg-neg = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-divideInteger-neg-neg ≡ expected-divideInteger-neg-neg
_ = refl
```

## divideInteger-neg-pos

```
-- builtin/semantics/divideInteger/divideInteger-neg-pos
test-divideInteger-neg-pos : Untyped
test-divideInteger-neg-pos = (UApp (UApp (UBuiltin divideInteger) (UCon (tagCon integer (ℤ.negsuc 502)))) (UCon (tagCon integer (ℤ.pos 1777777777))))

expected-divideInteger-neg-pos : Result
expected-divideInteger-neg-pos = success (UCon (tagCon integer (ℤ.negsuc 0)))

_ : evalRaw test-divideInteger-neg-pos ≡ expected-divideInteger-neg-pos
_ = refl
```

## divideInteger-pos-neg

```
-- builtin/semantics/divideInteger/divideInteger-pos-neg
test-divideInteger-pos-neg : Untyped
test-divideInteger-pos-neg = (UApp (UApp (UBuiltin divideInteger) (UCon (tagCon integer (ℤ.pos 503)))) (UCon (tagCon integer (ℤ.negsuc 1777777776))))

expected-divideInteger-pos-neg : Result
expected-divideInteger-pos-neg = success (UCon (tagCon integer (ℤ.negsuc 0)))

_ : evalRaw test-divideInteger-pos-neg ≡ expected-divideInteger-pos-neg
_ = refl
```

## divideInteger-pos-pos

```
-- builtin/semantics/divideInteger/divideInteger-pos-pos
test-divideInteger-pos-pos : Untyped
test-divideInteger-pos-pos = (UApp (UApp (UBuiltin divideInteger) (UCon (tagCon integer (ℤ.pos 503)))) (UCon (tagCon integer (ℤ.pos 1777777777))))

expected-divideInteger-pos-pos : Result
expected-divideInteger-pos-pos = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-divideInteger-pos-pos ≡ expected-divideInteger-pos-pos
_ = refl
```

## divideInteger-zero

```
-- builtin/semantics/divideInteger/divideInteger-zero
test-divideInteger-zero : Untyped
test-divideInteger-zero = (UApp (UApp (UBuiltin divideInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 0))))

expected-divideInteger-zero : Result
expected-divideInteger-zero = failure

_ : evalRaw test-divideInteger-zero ≡ expected-divideInteger-zero
_ = refl
```
