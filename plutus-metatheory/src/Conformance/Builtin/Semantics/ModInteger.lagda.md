---
title: Conformance.Builtin.Semantics.ModInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/modInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ModInteger where

open import Conformance.Eval
```

## modInteger-01

```
-- builtin/semantics/modInteger/modInteger-01
test-modInteger-01 : Untyped
test-modInteger-01 = (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 3))))

expected-modInteger-01 : Result
expected-modInteger-01 = success (UCon (tagCon integer (ℤ.pos 2)))

_ : evalRaw test-modInteger-01 ≡ expected-modInteger-01
_ = refl
```

## modInteger-neg-neg

```
-- builtin/semantics/modInteger/modInteger-neg-neg
test-modInteger-neg-neg : Untyped
test-modInteger-neg-neg = (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.negsuc 502)))) (UCon (tagCon integer (ℤ.negsuc 1777777776))))

expected-modInteger-neg-neg : Result
expected-modInteger-neg-neg = success (UCon (tagCon integer (ℤ.negsuc 502)))

_ : evalRaw test-modInteger-neg-neg ≡ expected-modInteger-neg-neg
_ = refl
```

## modInteger-neg-pos

```
-- builtin/semantics/modInteger/modInteger-neg-pos
test-modInteger-neg-pos : Untyped
test-modInteger-neg-pos = (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.negsuc 502)))) (UCon (tagCon integer (ℤ.pos 1777777777))))

expected-modInteger-neg-pos : Result
expected-modInteger-neg-pos = success (UCon (tagCon integer (ℤ.pos 1777777274)))

_ : evalRaw test-modInteger-neg-pos ≡ expected-modInteger-neg-pos
_ = refl
```

## modInteger-pos-neg

```
-- builtin/semantics/modInteger/modInteger-pos-neg
test-modInteger-pos-neg : Untyped
test-modInteger-pos-neg = (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.pos 503)))) (UCon (tagCon integer (ℤ.negsuc 1777777776))))

expected-modInteger-pos-neg : Result
expected-modInteger-pos-neg = success (UCon (tagCon integer (ℤ.negsuc 1777777273)))

_ : evalRaw test-modInteger-pos-neg ≡ expected-modInteger-pos-neg
_ = refl
```

## modInteger-pos-pos

```
-- builtin/semantics/modInteger/modInteger-pos-pos
test-modInteger-pos-pos : Untyped
test-modInteger-pos-pos = (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.pos 503)))) (UCon (tagCon integer (ℤ.pos 1777777777))))

expected-modInteger-pos-pos : Result
expected-modInteger-pos-pos = success (UCon (tagCon integer (ℤ.pos 503)))

_ : evalRaw test-modInteger-pos-pos ≡ expected-modInteger-pos-pos
_ = refl
```

## modInteger-zero

```
-- builtin/semantics/modInteger/modInteger-zero
test-modInteger-zero : Untyped
test-modInteger-zero = (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 0))))

expected-modInteger-zero : Result
expected-modInteger-zero = failure

_ : evalRaw test-modInteger-zero ≡ expected-modInteger-zero
_ = refl
```
