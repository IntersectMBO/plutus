---
title: Conformance.Term.ConstantCase.Integer
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/constant-case/integer`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.ConstantCase.Integer where

open import Conformance.Eval
```

## integer-01

```
-- term/constant-case/integer/integer-01
-- case on integer with no cases fails
test-integer-01 : Untyped
test-integer-01 = (UCase (UCon (tagCon integer (ℤ.pos 0))) ([]))

expected-integer-01 : Result
expected-integer-01 = failure

_ : evalRaw test-integer-01 ≡ expected-integer-01
_ = refl
```

## integer-02

```
-- term/constant-case/integer/integer-02
-- case on integer second branch
test-integer-02 : Untyped
test-integer-02 = (UCase (UCon (tagCon integer (ℤ.pos 1))) ((UCon (tagCon integer (ℤ.pos 42))) ∷ (UCon (tagCon integer (ℤ.pos 43))) ∷ (UCon (tagCon integer (ℤ.pos 443))) ∷ []))

expected-integer-02 : Result
expected-integer-02 = success (UCon (tagCon integer (ℤ.pos 43)))

_ : evalRaw test-integer-02 ≡ expected-integer-02
_ = refl
```

## integer-03

```
-- term/constant-case/integer/integer-03
-- case on integer fails when given integer is bigger than number of branches given
test-integer-03 : Untyped
test-integer-03 = (UCase (UCon (tagCon integer (ℤ.pos 3))) ((UCon (tagCon integer (ℤ.pos 42))) ∷ (UCon (tagCon integer (ℤ.pos 43))) ∷ (UCon (tagCon integer (ℤ.pos 44))) ∷ []))

expected-integer-03 : Result
expected-integer-03 = failure

_ : evalRaw test-integer-03 ≡ expected-integer-03
_ = refl
```

## integer-04

```
-- term/constant-case/integer/integer-04
-- case on negative integer fails
test-integer-04 : Untyped
test-integer-04 = (UCase (UCon (tagCon integer (ℤ.negsuc 0))) ((UCon (tagCon integer (ℤ.pos 42))) ∷ (UCon (tagCon integer (ℤ.pos 43))) ∷ (UCon (tagCon integer (ℤ.pos 44))) ∷ []))

expected-integer-04 : Result
expected-integer-04 = failure

_ : evalRaw test-integer-04 ≡ expected-integer-04
_ = refl
```
