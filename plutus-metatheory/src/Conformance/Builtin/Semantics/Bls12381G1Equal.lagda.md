---
title: Conformance.Builtin.Semantics.Bls12381G1Equal
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
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G1_equal`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G1Equal where

open import Conformance.Eval
```

## equal-false

```
-- builtin/semantics/bls12_381_G1_equal/equal-false
test-equal-false : Untyped
<<<<<<< HEAD
test-equal-false = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))
=======
test-equal-false = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))))
>>>>>>> origin/master

expected-equal-false : Result
expected-equal-false = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-equal-false : Set
pending-equal-false = Pending (evalRaw test-equal-false ≡ expected-equal-false)
```

## equal-true

```
-- builtin/semantics/bls12_381_G1_equal/equal-true
test-equal-true : Untyped
<<<<<<< HEAD
test-equal-true = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))
=======
test-equal-true = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))))
>>>>>>> origin/master

expected-equal-true : Result
expected-equal-true = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-uncompress`.
>>>>>>> origin/master
pending-equal-true : Set
pending-equal-true = Pending (evalRaw test-equal-true ≡ expected-equal-true)
```
