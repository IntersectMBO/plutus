---
title: Conformance.Term.ConstantCase.Data
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/constant-case/data`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.ConstantCase.Data where

open import Conformance.Eval
```

## data-01

```
-- term/constant-case/data/data-01
-- case on Data.Constr with no fields
test-data-01 : Untyped
test-data-01 = (UCase (UCon (tagCon pdata (ConstrDATA (ℤ.pos 0) ([])))) ((ULambda (UCon (tagCon integer (ℤ.pos 42)))) ∷ []))

expected-data-01 : Result
expected-data-01 = success (UCon (tagCon integer (ℤ.pos 42)))

-- Pending: casing on `data` constants is not supported by the Agda CEK machine yet.
pending-data-01 : Set
pending-data-01 = Pending (evalRaw test-data-01 ≡ expected-data-01)
```

## data-02

```
-- term/constant-case/data/data-02
-- select the second Data.Constr branch and pass its fields to the handler
test-data-02 : Untyped
test-data-02 = (UCase (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 42)) ∷ (bDATA (mkByteString "\171\205")) ∷ (ListDATA ((iDATA (ℤ.pos 7)) ∷ [])) ∷ [])))) ((ULambda (UCon (tagCon integer (ℤ.pos 0)))) ∷ (ULambda (UVar 0)) ∷ []))

expected-data-02 : Result
expected-data-02 = success (UCon (tagCon (list pdata) ((iDATA (ℤ.pos 42)) ∷ (bDATA (mkByteString "\171\205")) ∷ (ListDATA ((iDATA (ℤ.pos 7)) ∷ [])) ∷ [])))

-- Pending: bytestring inside a `data` constant; casing on `data` constants is not supported by the Agda CEK machine yet.
pending-data-02 : Set
pending-data-02 = Pending (evalRaw test-data-02 ≡ expected-data-02)
```

## data-03

```
-- term/constant-case/data/data-03
-- Data.Constr tag is out of bounds
test-data-03 : Untyped
test-data-03 = (UCase (UCon (tagCon pdata (ConstrDATA (ℤ.pos 2) ([])))) ((ULambda (UVar 0)) ∷ (ULambda (UVar 0)) ∷ []))

expected-data-03 : Result
expected-data-03 = failure

-- Pending: casing on `data` constants is not supported by the Agda CEK machine yet.
pending-data-03 : Set
pending-data-03 = Pending (evalRaw test-data-03 ≡ expected-data-03)
```

## data-04

```
-- term/constant-case/data/data-04
-- the selected handler must accept the Data.Constr fields
test-data-04 : Untyped
test-data-04 = (UCase (UCon (tagCon pdata (ConstrDATA (ℤ.pos 0) ([])))) ((UCon (tagCon integer (ℤ.pos 42))) ∷ []))

expected-data-04 : Result
expected-data-04 = failure

-- Pending: casing on `data` constants is not supported by the Agda CEK machine yet.
pending-data-04 : Set
pending-data-04 = Pending (evalRaw test-data-04 ≡ expected-data-04)
```

## data-05

```
-- term/constant-case/data/data-05
-- case on Data only supports Data.Constr values
test-data-05 : Untyped
test-data-05 = (UCase (UCon (tagCon pdata (iDATA (ℤ.pos 42)))) ((ULambda (UVar 0)) ∷ []))

expected-data-05 : Result
expected-data-05 = failure

-- Pending: casing on `data` constants is not supported by the Agda CEK machine yet.
pending-data-05 : Set
pending-data-05 = Pending (evalRaw test-data-05 ≡ expected-data-05)
```
