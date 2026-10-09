---
title: Conformance.Term.ConstantCase.Bool
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/constant-case/bool`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.ConstantCase.Bool where

open import Conformance.Eval
```

## bool-01

```
-- term/constant-case/bool/bool-01
-- case on false
test-bool-01 : Untyped
test-bool-01 = (UCase (UCon (tagCon bool false)) ((UCon (tagCon integer (ℤ.pos 0))) ∷ (UCon (tagCon integer (ℤ.pos 1))) ∷ []))

expected-bool-01 : Result
expected-bool-01 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-bool-01 ≡ expected-bool-01
_ = refl
```

## bool-02

```
-- term/constant-case/bool/bool-02
-- case on true
test-bool-02 : Untyped
test-bool-02 = (UCase (UCon (tagCon bool true)) ((UCon (tagCon integer (ℤ.pos 0))) ∷ (UCon (tagCon integer (ℤ.pos 1))) ∷ []))

expected-bool-02 : Result
expected-bool-02 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-bool-02 ≡ expected-bool-02
_ = refl
```

## bool-03

```
-- term/constant-case/bool/bool-03
-- case on false, one branch
test-bool-03 : Untyped
test-bool-03 = (UCase (UCon (tagCon bool false)) ((UCon (tagCon integer (ℤ.pos 0))) ∷ []))

expected-bool-03 : Result
expected-bool-03 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-bool-03 ≡ expected-bool-03
_ = refl
```

## bool-04

```
-- term/constant-case/bool/bool-04
-- case on true, one branch. Fails
test-bool-04 : Untyped
test-bool-04 = (UCase (UCon (tagCon bool true)) ((UCon (tagCon integer (ℤ.pos 0))) ∷ []))

expected-bool-04 : Result
expected-bool-04 = failure

_ : evalRaw test-bool-04 ≡ expected-bool-04
_ = refl
```

## bool-05

```
-- term/constant-case/bool/bool-05
-- case on False with 3+ branches fails
test-bool-05 : Untyped
test-bool-05 = (UCase (UCon (tagCon bool false)) ((UCon (tagCon integer (ℤ.pos 0))) ∷ (UCon (tagCon integer (ℤ.pos 1))) ∷ (UCon (tagCon integer (ℤ.pos 2))) ∷ []))

expected-bool-05 : Result
expected-bool-05 = failure

_ : evalRaw test-bool-05 ≡ expected-bool-05
_ = refl
```

## bool-06

```
-- term/constant-case/bool/bool-06
-- case on True with 3+ branches fails
test-bool-06 : Untyped
test-bool-06 = (UCase (UCon (tagCon bool true)) ((UCon (tagCon integer (ℤ.pos 0))) ∷ (UCon (tagCon integer (ℤ.pos 1))) ∷ (UCon (tagCon integer (ℤ.pos 2))) ∷ []))

expected-bool-06 : Result
expected-bool-06 = failure

_ : evalRaw test-bool-06 ≡ expected-bool-06
_ = refl
```

## bool-07

```
-- term/constant-case/bool/bool-07
-- case on boolean with no branches fails
test-bool-07 : Untyped
test-bool-07 = (UCase (UCon (tagCon bool false)) ([]))

expected-bool-07 : Result
expected-bool-07 = failure

_ : evalRaw test-bool-07 ≡ expected-bool-07
_ = refl
```
