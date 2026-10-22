---
title: Conformance.Term.Force
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/force`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.Force where

open import Conformance.Eval
```

## force-1

```
-- term/force/force-1
-- can only force a delay or a forceable (polymorphic) builtin
test-force-1 : Untyped
test-force-1 = (UForce (UCon (tagCon integer (ℤ.pos 5))))

expected-force-1 : Result
expected-force-1 = failure

_ : evalRaw test-force-1 ≡ expected-force-1
_ = refl
```

## force-2

```
-- term/force/force-2
test-force-2 : Untyped
test-force-2 = (UApp (ULambda (UForce (UVar 0))) (UDelay (UCon (tagCon integer (ℤ.pos 4)))))

expected-force-2 : Result
expected-force-2 = success (UCon (tagCon integer (ℤ.pos 4)))

_ : evalRaw test-force-2 ≡ expected-force-2
_ = refl
```

## force-3

```
-- term/force/force-3
test-force-3 : Untyped
test-force-3 = (UApp (ULambda (UForce (UApp (ULambda (UVar 0)) (UVar 0)))) (UDelay (UCon (tagCon integer (ℤ.pos 4)))))

expected-force-3 : Result
expected-force-3 = success (UCon (tagCon integer (ℤ.pos 4)))

_ : evalRaw test-force-3 ≡ expected-force-3
_ = refl
```

## force-4

```
-- term/force/force-4
test-force-4 : Untyped
test-force-4 = (UForce (ULambda (UVar 0)))

expected-force-4 : Result
expected-force-4 = failure

_ : evalRaw test-force-4 ≡ expected-force-4
_ = refl
```
