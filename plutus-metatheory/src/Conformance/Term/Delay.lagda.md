---
title: Conformance.Term.Delay
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/delay`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.Delay where

open import Conformance.Eval
```

## delay-error-1

```
-- term/delay/delay-error-1
test-delay-error-1 : Untyped
test-delay-error-1 = (UApp (ULambda (UCon (tagCon integer (ℤ.pos 4)))) (UDelay UError))

expected-delay-error-1 : Result
expected-delay-error-1 = success (UCon (tagCon integer (ℤ.pos 4)))

_ : evalRaw test-delay-error-1 ≡ expected-delay-error-1
_ = refl
```

## delay-error-2

```
-- term/delay/delay-error-2
test-delay-error-2 : Untyped
test-delay-error-2 = (UApp (ULambda (UVar 0)) (UDelay UError))

expected-delay-error-2 : Result
expected-delay-error-2 = success (UDelay UError)

_ : evalRaw test-delay-error-2 ≡ expected-delay-error-2
_ = refl
```

## delay-lam

```
-- term/delay/delay-lam
test-delay-lam : Untyped
test-delay-lam = (ULambda (UDelay (UVar 0)))

expected-delay-lam : Result
expected-delay-lam = success (ULambda (UDelay (UVar 0)))

_ : evalRaw test-delay-lam ≡ expected-delay-lam
_ = refl
```
