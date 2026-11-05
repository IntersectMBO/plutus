---
title: Conformance.Builtin.Semantics.AppendByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
<<<<<<< HEAD
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
=======
     Regenerate with `generate-agda-typecheck-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-typecheck-conformance` from the
>>>>>>> origin/master
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/appendByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.AppendByteString where

open import Conformance.Eval
```

## appendByteString-01

```
-- builtin/semantics/appendByteString/appendByteString-01
test-appendByteString-01 : Untyped
<<<<<<< HEAD
test-appendByteString-01 = (UApp (UApp (UBuiltin appendByteString) (UCon (tagCon bytestring (mkByteString "00aabbcc")))) (UCon (tagCon bytestring (mkByteString "ff0033"))))

expected-appendByteString-01 : Result
expected-appendByteString-01 = success (UCon (tagCon bytestring (mkByteString "00aabbccff0033")))

_ : evalRaw test-appendByteString-01 ≡ expected-appendByteString-01
_ = refl
=======
test-appendByteString-01 = (UApp (UApp (UBuiltin appendByteString) (UCon (tagCon bytestring (mkByteString "\NUL\170\187\204")))) (UCon (tagCon bytestring (mkByteString "\255\NUL3"))))

expected-appendByteString-01 : Result
expected-appendByteString-01 = success (UCon (tagCon bytestring (mkByteString "\NUL\170\187\204\255\NUL3")))

-- Pending: bytestring constant; postulated builtin `appendByteString`.
pending-appendByteString-01 : Set
pending-appendByteString-01 = Pending (evalRaw test-appendByteString-01 ≡ expected-appendByteString-01)
>>>>>>> origin/master
```

## appendByteString-02

```
-- builtin/semantics/appendByteString/appendByteString-02
test-appendByteString-02 : Untyped
<<<<<<< HEAD
test-appendByteString-02 = (UApp (UApp (UBuiltin appendByteString) (UCon (tagCon bytestring (mkByteString "00aabbcc")))) (UCon (tagCon bytestring (mkByteString ""))))

expected-appendByteString-02 : Result
expected-appendByteString-02 = success (UCon (tagCon bytestring (mkByteString "00aabbcc")))

_ : evalRaw test-appendByteString-02 ≡ expected-appendByteString-02
_ = refl
=======
test-appendByteString-02 = (UApp (UApp (UBuiltin appendByteString) (UCon (tagCon bytestring (mkByteString "\NUL\170\187\204")))) (UCon (tagCon bytestring (mkByteString ""))))

expected-appendByteString-02 : Result
expected-appendByteString-02 = success (UCon (tagCon bytestring (mkByteString "\NUL\170\187\204")))

-- Pending: bytestring constant; postulated builtin `appendByteString`.
pending-appendByteString-02 : Set
pending-appendByteString-02 = Pending (evalRaw test-appendByteString-02 ≡ expected-appendByteString-02)
>>>>>>> origin/master
```

## appendByteString-03

```
-- builtin/semantics/appendByteString/appendByteString-03
test-appendByteString-03 : Untyped
<<<<<<< HEAD
test-appendByteString-03 = (UApp (UApp (UBuiltin appendByteString) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "ff0033"))))

expected-appendByteString-03 : Result
expected-appendByteString-03 = success (UCon (tagCon bytestring (mkByteString "ff0033")))

_ : evalRaw test-appendByteString-03 ≡ expected-appendByteString-03
_ = refl
=======
test-appendByteString-03 = (UApp (UApp (UBuiltin appendByteString) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "\255\NUL3"))))

expected-appendByteString-03 : Result
expected-appendByteString-03 = success (UCon (tagCon bytestring (mkByteString "\255\NUL3")))

-- Pending: bytestring constant; postulated builtin `appendByteString`.
pending-appendByteString-03 : Set
pending-appendByteString-03 = Pending (evalRaw test-appendByteString-03 ≡ expected-appendByteString-03)
>>>>>>> origin/master
```
