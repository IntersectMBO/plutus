---
title: Conformance.Term.Constr
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/constr`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.Constr where

open import Conformance.Eval
```

## constr-01

```
-- term/constr/constr-01
-- empty constr
test-constr-01 : Untyped
test-constr-01 = (UConstr 0 ([]))

expected-constr-01 : Result
expected-constr-01 = success (UConstr 0 ([]))

_ : evalRaw test-constr-01 ≡ expected-constr-01
_ = refl
```

## constr-02

```
-- term/constr/constr-02
-- constr with an argument
test-constr-02 : Untyped
test-constr-02 = (UConstr 0 ((UCon (tagCon integer (ℤ.pos 1))) ∷ []))

expected-constr-02 : Result
expected-constr-02 = success (UConstr 0 ((UCon (tagCon integer (ℤ.pos 1))) ∷ []))

_ : evalRaw test-constr-02 ≡ expected-constr-02
_ = refl
```

## constr-03

```
-- term/constr/constr-03
-- constr can have arbitrary terms in it
test-constr-03 : Untyped
test-constr-03 = (UConstr 1 ((UCon (tagCon integer (ℤ.pos 1))) ∷ (ULambda (UVar 0)) ∷ (UConstr 0 ((UCon (tagCon integer (ℤ.pos 1))) ∷ [])) ∷ []))

expected-constr-03 : Result
expected-constr-03 = success (UConstr 1 ((UCon (tagCon integer (ℤ.pos 1))) ∷ (ULambda (UVar 0)) ∷ (UConstr 0 ((UCon (tagCon integer (ℤ.pos 1))) ∷ [])) ∷ []))

_ : evalRaw test-constr-03 ≡ expected-constr-03
_ = refl
```

## constr-04

```
-- term/constr/constr-04
-- constr is strict in all its arguments
test-constr-04 : Untyped
test-constr-04 = (UConstr 0 (UError ∷ []))

expected-constr-04 : Result
expected-constr-04 = failure

_ : evalRaw test-constr-04 ≡ expected-constr-04
_ = refl
```

## constr-05

```
-- term/constr/constr-05
-- constr is strict in all its arguments
test-constr-05 : Untyped
test-constr-05 = (UConstr 50000 ((UCon (tagCon integer (ℤ.pos 1))) ∷ UError ∷ []))

expected-constr-05 : Result
expected-constr-05 = failure

_ : evalRaw test-constr-05 ≡ expected-constr-05
_ = refl
```

## constr-06

Skipped: the program does not parse or has free variables (`parse/decode error`).

## constr-07

```
-- term/constr/constr-07
-- Tag can be as large as 2^64-1 = maxBound :: Word64
test-constr-07 : Untyped
test-constr-07 = (UConstr 18446744073709551615 ((UCon (tagCon string "Maximum tag = 2^64-1")) ∷ (UCon (tagCon integer (ℤ.pos 999))) ∷ []))

expected-constr-07 : Result
expected-constr-07 = success (UConstr 18446744073709551615 ((UCon (tagCon string "Maximum tag = 2^64-1")) ∷ (UCon (tagCon integer (ℤ.pos 999))) ∷ []))

_ : evalRaw test-constr-07 ≡ expected-constr-07
_ = refl
```

## constr-08

Skipped: the program does not parse or has free variables (`parse/decode error`).

## constr-09

Skipped: the program does not parse or has free variables (`parse/decode error`).
