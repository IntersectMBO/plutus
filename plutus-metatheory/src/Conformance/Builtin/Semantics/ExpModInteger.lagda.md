---
title: Conformance.Builtin.Semantics.ExpModInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/expModInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ExpModInteger where

open import Conformance.Eval
```

## exp-neg-non-inverse-01

```
-- builtin/semantics/expModInteger/exp-neg-non-inverse-01
test-exp-neg-non-inverse-01 : Untyped
test-exp-neg-non-inverse-01 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.negsuc 2)))) (UCon (tagCon integer (ℤ.negsuc 3))))

expected-exp-neg-non-inverse-01 : Result
expected-exp-neg-non-inverse-01 = failure

-- Pending: postulated builtin `expModInteger`.
pending-exp-neg-non-inverse-01 : Set
pending-exp-neg-non-inverse-01 = Pending (evalRaw test-exp-neg-non-inverse-01 ≡ expected-exp-neg-non-inverse-01)
```

## exp-neg-non-inverse-02

```
-- builtin/semantics/expModInteger/exp-neg-non-inverse-02
test-exp-neg-non-inverse-02 : Untyped
test-exp-neg-non-inverse-02 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 500)))) (UCon (tagCon integer (ℤ.negsuc 4)))) (UCon (tagCon integer (ℤ.pos 5))))

expected-exp-neg-non-inverse-02 : Result
expected-exp-neg-non-inverse-02 = failure

-- Pending: postulated builtin `expModInteger`.
pending-exp-neg-non-inverse-02 : Set
pending-exp-neg-non-inverse-02 = Pending (evalRaw test-exp-neg-non-inverse-02 ≡ expected-exp-neg-non-inverse-02)
```

## expMod-01

```
-- builtin/semantics/expModInteger/expMod-01
test-expMod-01 : Untyped
test-expMod-01 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 500)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 500))))

expected-expMod-01 : Result
expected-expMod-01 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expMod-01 : Set
pending-expMod-01 = Pending (evalRaw test-expMod-01 ≡ expected-expMod-01)
```

## expMod-02

```
-- builtin/semantics/expModInteger/expMod-02
test-expMod-02 : Untyped
test-expMod-02 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 500)))) (UCon (tagCon integer (ℤ.pos 5)))) (UCon (tagCon integer (ℤ.pos 500))))

expected-expMod-02 : Result
expected-expMod-02 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: postulated builtin `expModInteger`.
pending-expMod-02 : Set
pending-expMod-02 = Pending (evalRaw test-expMod-02 ≡ expected-expMod-02)
```

## expMod-03

```
-- builtin/semantics/expModInteger/expMod-03
test-expMod-03 : Untyped
test-expMod-03 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.negsuc 2)))) (UCon (tagCon integer (ℤ.pos 4))))

expected-expMod-03 : Result
expected-expMod-03 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expMod-03 : Set
pending-expMod-03 = Pending (evalRaw test-expMod-03 ≡ expected-expMod-03)
```

## expMod-04

```
-- builtin/semantics/expModInteger/expMod-04
test-expMod-04 : Untyped
test-expMod-04 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.negsuc 2)))) (UCon (tagCon integer (ℤ.pos 3))))

expected-expMod-04 : Result
expected-expMod-04 = success (UCon (tagCon integer (ℤ.pos 2)))

-- Pending: postulated builtin `expModInteger`.
pending-expMod-04 : Set
pending-expMod-04 = Pending (evalRaw test-expMod-04 ≡ expected-expMod-04)
```

## expMod-05

```
-- builtin/semantics/expModInteger/expMod-05
test-expMod-05 : Untyped
test-expMod-05 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 4)))) (UCon (tagCon integer (ℤ.negsuc 4)))) (UCon (tagCon integer (ℤ.pos 9))))

expected-expMod-05 : Result
expected-expMod-05 = success (UCon (tagCon integer (ℤ.pos 4)))

-- Pending: postulated builtin `expModInteger`.
pending-expMod-05 : Set
pending-expMod-05 = Pending (evalRaw test-expMod-05 ≡ expected-expMod-05)
```

## mod-neg

```
-- builtin/semantics/expModInteger/mod-neg
test-mod-neg : Untyped
test-mod-neg = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.negsuc 2))))

expected-mod-neg : Result
expected-mod-neg = failure

-- Pending: postulated builtin `expModInteger`.
pending-mod-neg : Set
pending-mod-neg = Pending (evalRaw test-mod-neg ≡ expected-mod-neg)
```

## mod-zero

```
-- builtin/semantics/expModInteger/mod-zero
test-mod-zero : Untyped
test-mod-zero = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 0))))

expected-mod-zero : Result
expected-mod-zero = failure

-- Pending: postulated builtin `expModInteger`.
pending-mod-zero : Set
pending-mod-zero = Pending (evalRaw test-mod-zero ≡ expected-mod-zero)
```
