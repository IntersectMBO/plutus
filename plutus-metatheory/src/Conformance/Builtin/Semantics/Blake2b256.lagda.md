---
title: Conformance.Builtin.Semantics.Blake2b256
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
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/blake2b_256`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Blake2b256 where

open import Conformance.Eval
```

## blake2b_256-empty

```
-- builtin/semantics/blake2b_256/blake2b_256-empty
-- Test vector (0-bit input) for Blake2b_256.
-- Output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
test-blake2b-256-empty : Untyped
<<<<<<< HEAD
test-blake2b-256-empty = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8"))))
=======
test-blake2b-256-empty = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\SOWQ\192&\229C\178\232\171.\176`\153\218\161\209\229\223Gw\143w\135\250\171E\205\241/\227\168"))))
>>>>>>> origin/master

expected-blake2b-256-empty : Result
expected-blake2b-256-empty = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `blake2b-256`.
=======
-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `blake2b-256`.
>>>>>>> origin/master
pending-blake2b-256-empty : Set
pending-blake2b-256-empty = Pending (evalRaw test-blake2b-256-empty ≡ expected-blake2b-256-empty)
```

## blake2b_256-length-200

```
-- builtin/semantics/blake2b_256/blake2b_256-length-200
-- Test vector (200-bit input) for Blake2b_256.
-- Output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
test-blake2b-256-length-200 : Untyped
<<<<<<< HEAD
test-blake2b-256-length-200 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-256) (UCon (tagCon bytestring (mkByteString "2e7ea84da4bc4d7cfb463e3f2c8647057afff3fbececa1d200"))))) (UCon (tagCon bytestring (mkByteString "91c60f99b33303c02b39ed93b713e3915a180c3747f3b31e05727618ee401624"))))
=======
test-blake2b-256-length-200 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-256) (UCon (tagCon bytestring (mkByteString ".~\168M\164\188M|\251F>?,\134G\ENQz\255\243\251\236\236\161\210\NUL"))))) (UCon (tagCon bytestring (mkByteString "\145\198\SI\153\179\&3\ETX\192+9\237\147\183\DC3\227\145Z\CAN\f7G\243\179\RS\ENQrv\CAN\238@\SYN$"))))
>>>>>>> origin/master

expected-blake2b-256-length-200 : Result
expected-blake2b-256-length-200 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `blake2b-256`.
=======
-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `blake2b-256`.
>>>>>>> origin/master
pending-blake2b-256-length-200 : Set
pending-blake2b-256-length-200 = Pending (evalRaw test-blake2b-256-length-200 ≡ expected-blake2b-256-length-200)
```
