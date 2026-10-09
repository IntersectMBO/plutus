---
title: Conformance.Builtin.Semantics.Bls12381G1Add
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G1_add`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G1Add where

open import Conformance.Eval
```

## add

```
-- builtin/semantics/bls12_381_G1_add/add
-- Adding a random pair of points in G1
test-add : Untyped
test-add = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245"))))))

expected-add : Result
expected-add = success (UCon (tagCon bytestring (mkByteString "\164\135\SO\152:\DC4\155\177\231\204p\253\233\a\162\170R0(3\188\228\214/g\152\EM\STX)$\233\202\171R\227c\GS7m6\217i&d\180\207\188\"")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-add : Set
pending-add = Pending (evalRaw test-add ≡ expected-add)
```

## add-associative

```
-- builtin/semantics/bls12_381_G1_add/add-associative
-- p+(q+r) = (p+q)+r for three random points on G1.
test-add-associative : Untyped
test-add-associative = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\185b\253\f\200\DLEH\224\207uW\191>Kn\220Z\180\191\179\220\135\248:\244(\182\&0\a'\177\&9\196\EOT\171\NAK\155\223.\174\163\246I\144\&4!S\DEL"))))))) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245")))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\185b\253\f\200\DLEH\224\207uW\191>Kn\220Z\180\191\179\220\135\248:\244(\182\&0\a'\177\&9\196\EOT\171\NAK\155\223.\174\163\246I\144\&4!S\DEL"))))))

expected-add-associative : Result
expected-add-associative = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-add-associative : Set
pending-add-associative = Pending (evalRaw test-add-associative ≡ expected-add-associative)
```

## add-commutative

```
-- builtin/semantics/bls12_381_G1_add/add-commutative
-- p+q = q+p for two random points in G1.
test-add-commutative : Untyped
test-add-commutative = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245")))))) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\149\r\253\&3\218&\130&\fv\ETX\141\251\139\173n\132\174\157Y\154<\NAK\CAN\NAK\148Z\193\230\239k\DLE'\205\145\DEL9\aG\157 \214\&6\206CzA\245"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))))

expected-add-commutative : Result
expected-add-commutative = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-add-commutative : Set
pending-add-commutative = Pending (evalRaw test-add-commutative ≡ expected-add-commutative)
```

## add-zero

```
-- builtin/semantics/bls12_381_G1_add/add-zero
-- Adding the zero element to a random point doesn't change it.
test-add-zero : Untyped
test-add-zero = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))))

expected-add-zero : Result
expected-add-zero = success (UCon (tagCon bytestring (mkByteString "\171\214\CANd\245\EMt\128\&2U\RSB\224\172A\DEL\216(\240yEN><\152\145\197\194\158\215\241\v\222\204\EOThT\227\147\FS\183\NUL'y\189v\215\US")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-add-zero : Set
pending-add-zero = Pending (evalRaw test-add-zero ≡ expected-add-zero)
```
