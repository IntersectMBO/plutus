---
title: Conformance.Term
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term where

open import Conformance.Eval
```

## argExpected

```
-- term/argExpected
-- addInteger is monomorphic so it must not be forced
test-argExpected : Untyped
test-argExpected = (UApp (UApp (UForce (UBuiltin addInteger)) (UCon (tagCon integer (ℤ.pos 5)))) (UCon (tagCon integer (ℤ.pos 6))))

expected-argExpected : Result
expected-argExpected = failure

_ : evalRaw test-argExpected ≡ expected-argExpected
_ = refl
```

## closure

```
-- term/closure
test-closure : Untyped
test-closure = (UApp (ULambda (ULambda (UVar 1))) (UCon (tagCon integer (ℤ.pos 1))))

expected-closure : Result
expected-closure = success (ULambda (UCon (tagCon integer (ℤ.pos 1))))

_ : evalRaw test-closure ≡ expected-closure
_ = refl
```

## nonFunctionalApplication

```
-- term/nonFunctionalApplication
test-nonFunctionalApplication : Untyped
test-nonFunctionalApplication = (UApp (UCon (tagCon integer (ℤ.pos 3))) (UCon (tagCon integer (ℤ.pos 4))))

expected-nonFunctionalApplication : Result
expected-nonFunctionalApplication = failure

_ : evalRaw test-nonFunctionalApplication ≡ expected-nonFunctionalApplication
_ = refl
```

## unlifting-sat

```
-- term/unlifting-sat
-- ill-typed. This fails at runtime since the builtin application is saturated.
test-unlifting-sat : Untyped
test-unlifting-sat = (UApp (UApp (UBuiltin addInteger) (UCon (tagCon unit tt))) (UCon (tagCon integer (ℤ.pos 3))))

expected-unlifting-sat : Result
expected-unlifting-sat = failure

_ : evalRaw test-unlifting-sat ≡ expected-unlifting-sat
_ = refl
```

## unlifting-unsat

```
-- term/unlifting-unsat
-- ill-typed but does not fail at runtime because the builtin application is not saturated.
test-unlifting-unsat : Untyped
test-unlifting-unsat = (UApp (UBuiltin addInteger) (UCon (tagCon unit tt)))

expected-unlifting-unsat : Result
expected-unlifting-unsat = success (UApp (UBuiltin addInteger) (UCon (tagCon unit tt)))

_ : evalRaw test-unlifting-unsat ≡ expected-unlifting-unsat
_ = refl
```

## var

Skipped: the program does not parse (`parse/decode error`).
