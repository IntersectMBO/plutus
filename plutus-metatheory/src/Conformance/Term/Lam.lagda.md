---
title: Conformance.Term.Lam
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/lam`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.Lam where

open import Conformance.Eval
```

## lam-1

```
-- term/lam/lam-1
test-lam-1 : Untyped
test-lam-1 = (ULambda (UVar 0))

expected-lam-1 : Result
expected-lam-1 = success (ULambda (UVar 0))

_ : evalRaw test-lam-1 ≡ expected-lam-1
_ = refl
```

## lam-2

```
-- term/lam/lam-2
test-lam-2 : Untyped
test-lam-2 = (ULambda (UCon (tagCon integer (ℤ.pos 23))))

expected-lam-2 : Result
expected-lam-2 = success (ULambda (UCon (tagCon integer (ℤ.pos 23))))

_ : evalRaw test-lam-2 ≡ expected-lam-2
_ = refl
```
