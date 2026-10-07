---
title: Conformance.Term.App
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/app`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.App where

open import Conformance.Eval
```

## app-1

```
-- term/app/app-1
test-app-1 : Untyped
test-app-1 = (UApp (ULambda (UVar 0)) (UCon (tagCon unit tt)))

expected-app-1 : Result
expected-app-1 = success (UCon (tagCon unit tt))

_ : evalRaw test-app-1 ≡ expected-app-1
_ = refl
```

## app-2

```
-- term/app/app-2
test-app-2 : Untyped
test-app-2 = (UApp (ULambda (UVar 0)) (UCon (tagCon integer (ℤ.pos 0))))

expected-app-2 : Result
expected-app-2 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-app-2 ≡ expected-app-2
_ = refl
```

## app-3

```
-- term/app/app-3
test-app-3 : Untyped
test-app-3 = (UApp (ULambda (UCon (tagCon bool false))) (UCon (tagCon integer (ℤ.pos 42))))

expected-app-3 : Result
expected-app-3 = success (UCon (tagCon bool false))

_ : evalRaw test-app-3 ≡ expected-app-3
_ = refl
```

## app-4

```
-- term/app/app-4
test-app-4 : Untyped
test-app-4 = (UApp (ULambda (UVar 0)) (UCon (tagCon integer (ℤ.pos 42))))

expected-app-4 : Result
expected-app-4 = success (UCon (tagCon integer (ℤ.pos 42)))

_ : evalRaw test-app-4 ≡ expected-app-4
_ = refl
```

## app-5

```
-- term/app/app-5
test-app-5 : Untyped
test-app-5 = (UApp (UApp (ULambda (UVar 0)) (ULambda (UVar 0))) (UCon (tagCon integer (ℤ.pos 42))))

expected-app-5 : Result
expected-app-5 = success (UCon (tagCon integer (ℤ.pos 42)))

_ : evalRaw test-app-5 ≡ expected-app-5
_ = refl
```

## app-6

```
-- term/app/app-6
test-app-6 : Untyped
test-app-6 = (UApp (ULambda (UVar 0)) (ULambda (UVar 0)))

expected-app-6 : Result
expected-app-6 = success (ULambda (UVar 0))

_ : evalRaw test-app-6 ≡ expected-app-6
_ = refl
```

## app-7

```
-- term/app/app-7
test-app-7 : Untyped
test-app-7 = (UApp (ULambda (ULambda (UVar 1))) (UCon (tagCon integer (ℤ.pos 42))))

expected-app-7 : Result
expected-app-7 = success (ULambda (UCon (tagCon integer (ℤ.pos 42))))

_ : evalRaw test-app-7 ≡ expected-app-7
_ = refl
```

## app-8

```
-- term/app/app-8
test-app-8 : Untyped
test-app-8 = (UApp (UApp (ULambda (ULambda (UVar 1))) (UCon (tagCon integer (ℤ.pos 42)))) (UCon (tagCon bool false)))

expected-app-8 : Result
expected-app-8 = success (UCon (tagCon integer (ℤ.pos 42)))

_ : evalRaw test-app-8 ≡ expected-app-8
_ = refl
```

## app-9

```
-- term/app/app-9
test-app-9 : Untyped
test-app-9 = (UApp (UApp (UApp (ULambda (ULambda (ULambda (UApp (UApp (UVar 2) (UVar 1)) (UVar 0))))) (ULambda (ULambda (UVar 1)))) (UCon (tagCon bool false))) (UCon (tagCon bool true)))

expected-app-9 : Result
expected-app-9 = success (UCon (tagCon bool false))

_ : evalRaw test-app-9 ≡ expected-app-9
_ = refl
```
