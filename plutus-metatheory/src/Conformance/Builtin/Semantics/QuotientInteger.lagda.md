---
title: Conformance.Builtin.Semantics.QuotientInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/quotientInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.QuotientInteger where

open import Conformance.Eval
```

## quotientInteger-01

```
-- builtin/semantics/quotientInteger/quotientInteger-01
test-quotientInteger-01 : Untyped
test-quotientInteger-01 = (UApp (UApp (UBuiltin quotientInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))

expected-quotientInteger-01 : Result
expected-quotientInteger-01 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-quotientInteger-01 ≡ expected-quotientInteger-01
_ = refl
```

## quotientInteger-neg-neg

```
-- builtin/semantics/quotientInteger/quotientInteger-neg-neg
test-quotientInteger-neg-neg : Untyped
test-quotientInteger-neg-neg = (UApp (UApp (UBuiltin quotientInteger) (UCon (tagCon integer (ℤ.negsuc 503783783785265728700234276)))) (UCon (tagCon integer (ℤ.negsuc 1777777776))))

expected-quotientInteger-neg-neg : Result
expected-quotientInteger-neg-neg = success (UCon (tagCon integer (ℤ.pos 283378378503190012)))

_ : evalRaw test-quotientInteger-neg-neg ≡ expected-quotientInteger-neg-neg
_ = refl
```

## quotientInteger-neg-pos

```
-- builtin/semantics/quotientInteger/quotientInteger-neg-pos
test-quotientInteger-neg-pos : Untyped
test-quotientInteger-neg-pos = (UApp (UApp (UBuiltin quotientInteger) (UCon (tagCon integer (ℤ.negsuc 503783783785265728700234276)))) (UCon (tagCon integer (ℤ.pos 1777777777))))

expected-quotientInteger-neg-pos : Result
expected-quotientInteger-neg-pos = success (UCon (tagCon integer (ℤ.negsuc 283378378503190011)))

_ : evalRaw test-quotientInteger-neg-pos ≡ expected-quotientInteger-neg-pos
_ = refl
```

## quotientInteger-pos-neg

```
-- builtin/semantics/quotientInteger/quotientInteger-pos-neg
test-quotientInteger-pos-neg : Untyped
test-quotientInteger-pos-neg = (UApp (UApp (UBuiltin quotientInteger) (UCon (tagCon integer (ℤ.pos 503783783785265728700234277)))) (UCon (tagCon integer (ℤ.negsuc 1777777776))))

expected-quotientInteger-pos-neg : Result
expected-quotientInteger-pos-neg = success (UCon (tagCon integer (ℤ.negsuc 283378378503190011)))

_ : evalRaw test-quotientInteger-pos-neg ≡ expected-quotientInteger-pos-neg
_ = refl
```

## quotientInteger-pos-pos

```
-- builtin/semantics/quotientInteger/quotientInteger-pos-pos
test-quotientInteger-pos-pos : Untyped
test-quotientInteger-pos-pos = (UApp (UApp (UBuiltin quotientInteger) (UCon (tagCon integer (ℤ.pos 503783783785265728700234277)))) (UCon (tagCon integer (ℤ.pos 1777777777))))

expected-quotientInteger-pos-pos : Result
expected-quotientInteger-pos-pos = success (UCon (tagCon integer (ℤ.pos 283378378503190012)))

_ : evalRaw test-quotientInteger-pos-pos ≡ expected-quotientInteger-pos-pos
_ = refl
```

## quotientInteger-zero

```
-- builtin/semantics/quotientInteger/quotientInteger-zero
test-quotientInteger-zero : Untyped
test-quotientInteger-zero = (UApp (UApp (UBuiltin quotientInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 0))))

expected-quotientInteger-zero : Result
expected-quotientInteger-zero = failure

_ : evalRaw test-quotientInteger-zero ≡ expected-quotientInteger-zero
_ = refl
```
