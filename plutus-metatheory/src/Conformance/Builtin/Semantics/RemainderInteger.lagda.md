---
title: Conformance.Builtin.Semantics.RemainderInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/remainderInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.RemainderInteger where

open import Conformance.Eval
```

## remainderInteger-01

```
-- builtin/semantics/remainderInteger/remainderInteger-01
test-remainderInteger-01 : Untyped
test-remainderInteger-01 = (UApp (UApp (UBuiltin remainderInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))

expected-remainderInteger-01 : Result
expected-remainderInteger-01 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-remainderInteger-01 ≡ expected-remainderInteger-01
_ = refl
```

## remainderInteger-neg-neg

```
-- builtin/semantics/remainderInteger/remainderInteger-neg-neg
test-remainderInteger-neg-neg : Untyped
test-remainderInteger-neg-neg = (UApp (UApp (UBuiltin remainderInteger) (UCon (tagCon integer (ℤ.negsuc 502)))) (UCon (tagCon integer (ℤ.negsuc 1777777776))))

expected-remainderInteger-neg-neg : Result
expected-remainderInteger-neg-neg = success (UCon (tagCon integer (ℤ.negsuc 502)))

_ : evalRaw test-remainderInteger-neg-neg ≡ expected-remainderInteger-neg-neg
_ = refl
```

## remainderInteger-neg-pos

```
-- builtin/semantics/remainderInteger/remainderInteger-neg-pos
test-remainderInteger-neg-pos : Untyped
test-remainderInteger-neg-pos = (UApp (UApp (UBuiltin remainderInteger) (UCon (tagCon integer (ℤ.negsuc 502)))) (UCon (tagCon integer (ℤ.pos 1777777777))))

expected-remainderInteger-neg-pos : Result
expected-remainderInteger-neg-pos = success (UCon (tagCon integer (ℤ.negsuc 502)))

_ : evalRaw test-remainderInteger-neg-pos ≡ expected-remainderInteger-neg-pos
_ = refl
```

## remainderInteger-pos-neg

```
-- builtin/semantics/remainderInteger/remainderInteger-pos-neg
test-remainderInteger-pos-neg : Untyped
test-remainderInteger-pos-neg = (UApp (UApp (UBuiltin remainderInteger) (UCon (tagCon integer (ℤ.pos 503)))) (UCon (tagCon integer (ℤ.negsuc 1777777776))))

expected-remainderInteger-pos-neg : Result
expected-remainderInteger-pos-neg = success (UCon (tagCon integer (ℤ.pos 503)))

_ : evalRaw test-remainderInteger-pos-neg ≡ expected-remainderInteger-pos-neg
_ = refl
```

## remainderInteger-pos-pos

```
-- builtin/semantics/remainderInteger/remainderInteger-pos-pos
test-remainderInteger-pos-pos : Untyped
test-remainderInteger-pos-pos = (UApp (UApp (UBuiltin remainderInteger) (UCon (tagCon integer (ℤ.pos 503)))) (UCon (tagCon integer (ℤ.pos 1777777777))))

expected-remainderInteger-pos-pos : Result
expected-remainderInteger-pos-pos = success (UCon (tagCon integer (ℤ.pos 503)))

_ : evalRaw test-remainderInteger-pos-pos ≡ expected-remainderInteger-pos-pos
_ = refl
```

## remainderInteger-zero

```
-- builtin/semantics/remainderInteger/remainderInteger-zero
test-remainderInteger-zero : Untyped
test-remainderInteger-zero = (UApp (UApp (UBuiltin remainderInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 0))))

expected-remainderInteger-zero : Result
expected-remainderInteger-zero = failure

_ : evalRaw test-remainderInteger-zero ≡ expected-remainderInteger-zero
_ = refl
```
