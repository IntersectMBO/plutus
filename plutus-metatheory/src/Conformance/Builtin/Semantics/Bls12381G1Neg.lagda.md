---
title: Conformance.Builtin.Semantics.Bls12381G1Neg
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G1_neg`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G1Neg where

open import Conformance.Eval
```

## add-neg

```
-- builtin/semantics/bls12_381_G1_neg/add-neg
-- Check that adding a random point to its negative gives the zero element.
test-add-neg : Untyped
test-add-neg = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245"))))) (UApp (UBuiltin bls12-381-G1-neg) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245")))))))

expected-add-neg : Result
expected-add-neg = success (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G1-neg`.
pending-add-neg : Set
pending-add-neg = Pending (evalRaw test-add-neg ≡ expected-add-neg)
```

## neg

```
-- builtin/semantics/bls12_381_G1_neg/neg
-- Check that negating a random point in G1 gives the expected result.
test-neg : Untyped
test-neg = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-neg) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))

expected-neg : Result
expected-neg = success (UCon (tagCon bytestring (mkByteString "\139\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-neg`; postulated builtin `bls12-381-G1-uncompress`.
pending-neg : Set
pending-neg = Pending (evalRaw test-neg ≡ expected-neg)
```

## neg-zero

```
-- builtin/semantics/bls12_381_G1_neg/neg-zero
-- The negative of the zero point is the zero point.
test-neg-zero : Untyped
test-neg-zero = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-neg) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))))

expected-neg-zero : Result
expected-neg-zero = success (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-neg`; postulated builtin `bls12-381-G1-uncompress`.
pending-neg-zero : Set
pending-neg-zero = Pending (evalRaw test-neg-zero ≡ expected-neg-zero)
```
