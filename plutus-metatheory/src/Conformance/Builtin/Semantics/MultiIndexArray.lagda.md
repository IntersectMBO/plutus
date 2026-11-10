---
title: Conformance.Builtin.Semantics.MultiIndexArray
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-typecheck-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-typecheck-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/multiIndexArray`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.MultiIndexArray where

open import Conformance.Eval
```

## multiIndexArray-01

```
-- builtin/semantics/multiIndexArray/multiIndexArray-01
-- Single lookup
test-multiIndexArray-01 : Untyped
test-multiIndexArray-01 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 2) ∷ []))))

expected-multiIndexArray-01 : Result
expected-multiIndexArray-01 = success (UCon (tagCon (list integer) ((ℤ.pos 30) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-01 : Set
pending-multiIndexArray-01 = Pending (evalRaw test-multiIndexArray-01 ≡ expected-multiIndexArray-01)
```

## multiIndexArray-02

```
-- builtin/semantics/multiIndexArray/multiIndexArray-02
-- First and last elements
test-multiIndexArray-02 : Untyped
test-multiIndexArray-02 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.pos 4) ∷ []))))

expected-multiIndexArray-02 : Result
expected-multiIndexArray-02 = success (UCon (tagCon (list integer) ((ℤ.pos 10) ∷ (ℤ.pos 50) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-02 : Set
pending-multiIndexArray-02 = Pending (evalRaw test-multiIndexArray-02 ≡ expected-multiIndexArray-02)
```

## multiIndexArray-03

```
-- builtin/semantics/multiIndexArray/multiIndexArray-03
-- Ascending selection
test-multiIndexArray-03 : Untyped
test-multiIndexArray-03 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ (ℤ.pos 4) ∷ []))))

expected-multiIndexArray-03 : Result
expected-multiIndexArray-03 = success (UCon (tagCon (list integer) ((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-03 : Set
pending-multiIndexArray-03 = Pending (evalRaw test-multiIndexArray-03 ≡ expected-multiIndexArray-03)
```

## multiIndexArray-04

```
-- builtin/semantics/multiIndexArray/multiIndexArray-04
-- Reversed selection
test-multiIndexArray-04 : Untyped
test-multiIndexArray-04 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 4) ∷ (ℤ.pos 3) ∷ (ℤ.pos 2) ∷ (ℤ.pos 1) ∷ (ℤ.pos 0) ∷ []))))

expected-multiIndexArray-04 : Result
expected-multiIndexArray-04 = success (UCon (tagCon (list integer) ((ℤ.pos 50) ∷ (ℤ.pos 40) ∷ (ℤ.pos 30) ∷ (ℤ.pos 20) ∷ (ℤ.pos 10) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-04 : Set
pending-multiIndexArray-04 = Pending (evalRaw test-multiIndexArray-04 ≡ expected-multiIndexArray-04)
```

## multiIndexArray-05

```
-- builtin/semantics/multiIndexArray/multiIndexArray-05
-- Nonadjacent selection
test-multiIndexArray-05 : Untyped
test-multiIndexArray-05 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.pos 2) ∷ (ℤ.pos 4) ∷ []))))

expected-multiIndexArray-05 : Result
expected-multiIndexArray-05 = success (UCon (tagCon (list integer) ((ℤ.pos 10) ∷ (ℤ.pos 30) ∷ (ℤ.pos 50) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-05 : Set
pending-multiIndexArray-05 = Pending (evalRaw test-multiIndexArray-05 ≡ expected-multiIndexArray-05)
```

## multiIndexArray-06

```
-- builtin/semantics/multiIndexArray/multiIndexArray-06
-- Duplicate indices are preserved
test-multiIndexArray-06 : Untyped
test-multiIndexArray-06 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 2) ∷ (ℤ.pos 2) ∷ (ℤ.pos 2) ∷ []))))

expected-multiIndexArray-06 : Result
expected-multiIndexArray-06 = success (UCon (tagCon (list integer) ((ℤ.pos 30) ∷ (ℤ.pos 30) ∷ (ℤ.pos 30) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-06 : Set
pending-multiIndexArray-06 = Pending (evalRaw test-multiIndexArray-06 ≡ expected-multiIndexArray-06)
```

## multiIndexArray-07

```
-- builtin/semantics/multiIndexArray/multiIndexArray-07
-- Mixed ordering and duplicates
test-multiIndexArray-07 : Untyped
test-multiIndexArray-07 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 4) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 2) ∷ (ℤ.pos 1) ∷ []))))

expected-multiIndexArray-07 : Result
expected-multiIndexArray-07 = success (UCon (tagCon (list integer) ((ℤ.pos 50) ∷ (ℤ.pos 10) ∷ (ℤ.pos 10) ∷ (ℤ.pos 30) ∷ (ℤ.pos 20) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-07 : Set
pending-multiIndexArray-07 = Pending (evalRaw test-multiIndexArray-07 ≡ expected-multiIndexArray-07)
```

## multiIndexArray-08

```
-- builtin/semantics/multiIndexArray/multiIndexArray-08
-- Empty indices with a nonempty array
test-multiIndexArray-08 : Untyped
test-multiIndexArray-08 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ([]))))

expected-multiIndexArray-08 : Result
expected-multiIndexArray-08 = success (UCon (tagCon (list integer) ([])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-08 : Set
pending-multiIndexArray-08 = Pending (evalRaw test-multiIndexArray-08 ≡ expected-multiIndexArray-08)
```

## multiIndexArray-09

```
-- builtin/semantics/multiIndexArray/multiIndexArray-09
-- Empty indices with an empty array
test-multiIndexArray-09 : Untyped
test-multiIndexArray-09 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (([])))))) (UCon (tagCon (list integer) ([]))))

expected-multiIndexArray-09 : Result
expected-multiIndexArray-09 = success (UCon (tagCon (list integer) ([])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-09 : Set
pending-multiIndexArray-09 = Pending (evalRaw test-multiIndexArray-09 ≡ expected-multiIndexArray-09)
```

## multiIndexArray-10

```
-- builtin/semantics/multiIndexArray/multiIndexArray-10
-- Nonempty indices with an empty array fail
test-multiIndexArray-10 : Untyped
test-multiIndexArray-10 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (([])))))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ []))))

expected-multiIndexArray-10 : Result
expected-multiIndexArray-10 = failure

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-10 : Set
pending-multiIndexArray-10 = Pending (evalRaw test-multiIndexArray-10 ≡ expected-multiIndexArray-10)
```

## multiIndexArray-11

```
-- builtin/semantics/multiIndexArray/multiIndexArray-11
-- Negative index fails
test-multiIndexArray-11 : Untyped
test-multiIndexArray-11 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.negsuc 0) ∷ []))))

expected-multiIndexArray-11 : Result
expected-multiIndexArray-11 = failure

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-11 : Set
pending-multiIndexArray-11 = Pending (evalRaw test-multiIndexArray-11 ≡ expected-multiIndexArray-11)
```

## multiIndexArray-12

```
-- builtin/semantics/multiIndexArray/multiIndexArray-12
-- Index equal to array length fails
test-multiIndexArray-12 : Untyped
test-multiIndexArray-12 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 5) ∷ []))))

expected-multiIndexArray-12 : Result
expected-multiIndexArray-12 = failure

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-12 : Set
pending-multiIndexArray-12 = Pending (evalRaw test-multiIndexArray-12 ≡ expected-multiIndexArray-12)
```

## multiIndexArray-13

```
-- builtin/semantics/multiIndexArray/multiIndexArray-13
-- Index greater than array length fails
test-multiIndexArray-13 : Untyped
test-multiIndexArray-13 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 6) ∷ []))))

expected-multiIndexArray-13 : Result
expected-multiIndexArray-13 = failure

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-13 : Set
pending-multiIndexArray-13 = Pending (evalRaw test-multiIndexArray-13 ≡ expected-multiIndexArray-13)
```

## multiIndexArray-14

```
-- builtin/semantics/multiIndexArray/multiIndexArray-14
-- Index beyond the machine integer range fails without wrapping
test-multiIndexArray-14 : Untyped
test-multiIndexArray-14 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 18446744073709551616) ∷ []))))

expected-multiIndexArray-14 : Result
expected-multiIndexArray-14 = failure

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-14 : Set
pending-multiIndexArray-14 = Pending (evalRaw test-multiIndexArray-14 ≡ expected-multiIndexArray-14)
```

## multiIndexArray-15

```
-- builtin/semantics/multiIndexArray/multiIndexArray-15
-- Negative index beyond the machine integer range fails
test-multiIndexArray-15 : Untyped
test-multiIndexArray-15 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.negsuc 18446744073709551615) ∷ []))))

expected-multiIndexArray-15 : Result
expected-multiIndexArray-15 = failure

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-15 : Set
pending-multiIndexArray-15 = Pending (evalRaw test-multiIndexArray-15 ≡ expected-multiIndexArray-15)
```

## multiIndexArray-16

```
-- builtin/semantics/multiIndexArray/multiIndexArray-16
-- An invalid index between valid lookups fails the whole call
test-multiIndexArray-16 : Untyped
test-multiIndexArray-16 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ (ℤ.pos 30) ∷ (ℤ.pos 40) ∷ (ℤ.pos 50) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.pos 5) ∷ (ℤ.pos 1) ∷ []))))

expected-multiIndexArray-16 : Result
expected-multiIndexArray-16 = failure

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-16 : Set
pending-multiIndexArray-16 = Pending (evalRaw test-multiIndexArray-16 ≡ expected-multiIndexArray-16)
```

## multiIndexArray-17

```
-- builtin/semantics/multiIndexArray/multiIndexArray-17
-- Exactly 1024 valid indices succeed
test-multiIndexArray-17 : Untyped
test-multiIndexArray-17 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 42) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ []))))

expected-multiIndexArray-17 : Result
expected-multiIndexArray-17 = success (UCon (tagCon (list integer) ((ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ (ℤ.pos 42) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-17 : Set
pending-multiIndexArray-17 = Pending (evalRaw test-multiIndexArray-17 ≡ expected-multiIndexArray-17)
```

## multiIndexArray-18

```
-- builtin/semantics/multiIndexArray/multiIndexArray-18
-- 1025 valid indices fail the count limit
test-multiIndexArray-18 : Untyped
test-multiIndexArray-18 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 42) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ (ℤ.pos 0) ∷ []))))

expected-multiIndexArray-18 : Result
expected-multiIndexArray-18 = failure

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-18 : Set
pending-multiIndexArray-18 = Pending (evalRaw test-multiIndexArray-18 ≡ expected-multiIndexArray-18)
```

## multiIndexArray-19

```
-- builtin/semantics/multiIndexArray/multiIndexArray-19
-- Boolean elements retain their values, order and duplicates
test-multiIndexArray-19 : Untyped
test-multiIndexArray-19 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array bool) (mkArray ((false ∷ true ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 0) ∷ (ℤ.pos 1) ∷ []))))

expected-multiIndexArray-19 : Result
expected-multiIndexArray-19 = success (UCon (tagCon (list bool) (true ∷ false ∷ true ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-19 : Set
pending-multiIndexArray-19 = Pending (evalRaw test-multiIndexArray-19 ≡ expected-multiIndexArray-19)
```

## multiIndexArray-20

```
-- builtin/semantics/multiIndexArray/multiIndexArray-20
-- Bytestring elements retain their values, order and duplicates
test-multiIndexArray-20 : Untyped
test-multiIndexArray-20 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array bytestring) (mkArray (((mkByteString "\NUL") ∷ (mkByteString "\255\SOH") ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 0) ∷ (ℤ.pos 1) ∷ []))))

expected-multiIndexArray-20 : Result
expected-multiIndexArray-20 = success (UCon (tagCon (list bytestring) ((mkByteString "\255\SOH") ∷ (mkByteString "\NUL") ∷ (mkByteString "\255\SOH") ∷ [])))

-- Pending: array constant; bytestring constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-20 : Set
pending-multiIndexArray-20 = Pending (evalRaw test-multiIndexArray-20 ≡ expected-multiIndexArray-20)
```

## multiIndexArray-21

```
-- builtin/semantics/multiIndexArray/multiIndexArray-21
-- String elements retain their values, order and duplicates
test-multiIndexArray-21 : Untyped
test-multiIndexArray-21 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array string) (mkArray (("alpha" ∷ "beta" ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 0) ∷ (ℤ.pos 1) ∷ []))))

expected-multiIndexArray-21 : Result
expected-multiIndexArray-21 = success (UCon (tagCon (list string) ("beta" ∷ "alpha" ∷ "beta" ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-21 : Set
pending-multiIndexArray-21 = Pending (evalRaw test-multiIndexArray-21 ≡ expected-multiIndexArray-21)
```

## multiIndexArray-22

```
-- builtin/semantics/multiIndexArray/multiIndexArray-22
-- Unit elements retain their values, order and duplicates
test-multiIndexArray-22 : Untyped
test-multiIndexArray-22 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array unit) (mkArray ((tt ∷ tt ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 0) ∷ (ℤ.pos 1) ∷ []))))

expected-multiIndexArray-22 : Result
expected-multiIndexArray-22 = success (UCon (tagCon (list unit) (tt ∷ tt ∷ tt ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-22 : Set
pending-multiIndexArray-22 = Pending (evalRaw test-multiIndexArray-22 ≡ expected-multiIndexArray-22)
```

## multiIndexArray-23

```
-- builtin/semantics/multiIndexArray/multiIndexArray-23
-- Data elements retain their values, order and duplicates
test-multiIndexArray-23 : Untyped
test-multiIndexArray-23 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array pdata) (mkArray (((ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 10)) ∷ [])) ∷ (ListDATA ((bDATA (mkByteString "\255")) ∷ (iDATA (ℤ.pos 20)) ∷ [])) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 0) ∷ (ℤ.pos 1) ∷ []))))

expected-multiIndexArray-23 : Result
expected-multiIndexArray-23 = success (UCon (tagCon (list pdata) ((ListDATA ((bDATA (mkByteString "\255")) ∷ (iDATA (ℤ.pos 20)) ∷ [])) ∷ (ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 10)) ∷ [])) ∷ (ListDATA ((bDATA (mkByteString "\255")) ∷ (iDATA (ℤ.pos 20)) ∷ [])) ∷ [])))

-- Pending: array constant; bytestring inside a `data` constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-23 : Set
pending-multiIndexArray-23 = Pending (evalRaw test-multiIndexArray-23 ≡ expected-multiIndexArray-23)
```

## multiIndexArray-24

```
-- builtin/semantics/multiIndexArray/multiIndexArray-24
-- List elements retain their values, order and duplicates
test-multiIndexArray-24 : Untyped
test-multiIndexArray-24 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array (list integer)) (mkArray ((((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ []) ∷ ([]) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 0) ∷ (ℤ.pos 1) ∷ []))))

expected-multiIndexArray-24 : Result
expected-multiIndexArray-24 = success (UCon (tagCon (list (list integer)) (([]) ∷ ((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ []) ∷ ([]) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-24 : Set
pending-multiIndexArray-24 = Pending (evalRaw test-multiIndexArray-24 ≡ expected-multiIndexArray-24)
```

## multiIndexArray-25

```
-- builtin/semantics/multiIndexArray/multiIndexArray-25
-- Pair elements retain their values, order and duplicates
test-multiIndexArray-25 : Untyped
test-multiIndexArray-25 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array (pair integer bool)) (mkArray ((((ℤ.pos 10) , false) ∷ ((ℤ.pos 20) , true) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 0) ∷ (ℤ.pos 1) ∷ []))))

expected-multiIndexArray-25 : Result
expected-multiIndexArray-25 = success (UCon (tagCon (list (pair integer bool)) (((ℤ.pos 20) , true) ∷ ((ℤ.pos 10) , false) ∷ ((ℤ.pos 20) , true) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-25 : Set
pending-multiIndexArray-25 = Pending (evalRaw test-multiIndexArray-25 ≡ expected-multiIndexArray-25)
```

## multiIndexArray-26

```
-- builtin/semantics/multiIndexArray/multiIndexArray-26
-- Nested array elements retain their values, order and duplicates
test-multiIndexArray-26 : Untyped
test-multiIndexArray-26 = (UApp (UApp (UForce (UBuiltin multiIndexArray)) (UCon (tagCon (array (array integer)) (mkArray (((mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ []))) ∷ (mkArray (([]))) ∷ [])))))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 0) ∷ (ℤ.pos 1) ∷ []))))

expected-multiIndexArray-26 : Result
expected-multiIndexArray-26 = success (UCon (tagCon (list (array integer)) ((mkArray (([]))) ∷ (mkArray (((ℤ.pos 10) ∷ (ℤ.pos 20) ∷ []))) ∷ (mkArray (([]))) ∷ [])))

-- Pending: array constant; postulated builtin `multiIndexArray`.
pending-multiIndexArray-26 : Set
pending-multiIndexArray-26 = Pending (evalRaw test-multiIndexArray-26 ≡ expected-multiIndexArray-26)
```
