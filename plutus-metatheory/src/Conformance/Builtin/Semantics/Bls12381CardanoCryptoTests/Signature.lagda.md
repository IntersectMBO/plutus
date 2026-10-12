---
title: Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.Signature
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381-cardano-crypto-tests/signature`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.Signature where

open import Conformance.Eval
```

## augmented

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/signature/augmented
-- Check that a signature involving an agumentation string prepended to a message
-- is as expected.
test-augmented : Untyped
test-augmented = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\131B/\209\216\241\&4\251\188z\210\148\154\v|8\220\US\133\191\211\152\188X\174\130J\211J\206h\234\164\159C\136r\238\"\233\axQ:\145\249h^"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\147\224+`Rq\159`}\172\211\160\136'OeYk\208\208\153 \182\SUB\181\218a\187\220\DELPI3L\241\DC2\DC3\148]W\229\172}\ENQ]\EOT+~\STXJ\162\178\240\143\n\145&\b\ENQ'-\197\DLEQ\198\228z\212\250@;\STX\180Q\vdz\227\209w\v\172\ETX&\168\ENQ\187\239\212\128V\200\193!\189\184")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UApp (UApp (UBuiltin appendByteString) (UCon (tagCon bytestring (mkByteString "Random value for test aug. ")))) (UCon (tagCon bytestring (mkByteString "blst is such a blast"))))) (UCon (tagCon bytestring (mkByteString "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\183V\214\":\146`\156\204\246`\182\243~n4\251\178\&9r\252\&9Uq\SI\155\178\STX\204\132\207\250\205\&3w\146p\SO\188\180\&2J\153\199\231\201\237m\SO\FS\253\206\140\216y\163S\NUL\149|i\197$\197\&6_o\n\133\DC3\a5\242u\DLEa\139\190\166\ENQ\161\208$\187-;\238*]h\168'@o\DC1\199"))))))

expected-augmented : Result
expected-augmented = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`; postulated builtin `bls12-381-G1-hashToGroup`; postulated builtin `appendByteString`.
pending-augmented : Set
pending-augmented = Pending (evalRaw test-augmented ≡ expected-augmented)
```

## large-dst

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/signature/large-dst
-- Check that the procedure for using a DST greater than 255 bytes long gives the expected result.
test-large-dst : Untyped
test-large-dst = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-hashToGroup) (UCon (tagCon bytestring (mkByteString "Testing large dst.")))) (UApp (UBuiltin sha2-256) (UApp (UApp (UBuiltin appendByteString) (UCon (tagCon bytestring (mkByteString "H2C-OVERSIZE-DST-")))) (UCon (tagCon bytestring (mkByteString "b\245\128@ \230\168\226B\199\&6\209\201{\205\130b\249\ESC\136\225\215\v\NUL\209\r^1\\\140e\SOH\234\208\167\227g\229\211\148\185\252\255\156\NAK\170\SIj\ENQ\229\b_\220V\188\222\227\134P\SYN\241\196\155 \225\230\t\166\ACK\236\202\188\155\145\153\164#E\194^\ACK\174p\STX\131\151\248\251\149Wo&B9\218>\180\150)\213\239\235\US\GSt\163\177\172X`\141\137?\152\ENQ\143Z\184p\131\&4\137\245\223\236R\219_\146\231\r\176\\\151\EOT\205\157dK\SUB\225j\170\252\193s\212\141\177~ }\145\&0\141\&0E\176B\183$\US\135\184\212*\197\223\151\217O\223?)\210\f\162\174\"\194.\156[\132\180\141m\175\USyY\199\199\GS\SOHi\243p\235\242\131\132y\179s\CAN\133\255\r'\141\235c/\203\131\174\240\171Y=\221\212\245\210\GS\172V\171\224\139\140\180\170\244#[\SUB)+\145\214\232\185\SO9\220\149<u\252F\SO}\214\210\188\138\&7*\196\239\206\SYN\US_\CAN\248a\230~W\ETB\200h\ENQ\160\\\197?\244\147\233\GS\226\184]1f\179S\245\187\198K\174\r*G\135"))))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\161kWx\181\184\133\EM\182\202\240Y!\208\217\184\185J3\209\218\170\f\DEL\191\166mR\232\SOH\165\231\152\250\232@\187\150\b\170\&1q.\v\ESC:\ENQJ")))))

expected-large-dst : Result
expected-large-dst = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-hashToGroup`; postulated builtin `sha2-256`; postulated builtin `appendByteString`; postulated builtin `bls12-381-G1-uncompress`.
pending-large-dst : Set
pending-large-dst = Pending (evalRaw test-large-dst ≡ expected-large-dst)
```
