---
title: Conformance.Builtin.Semantics.VerifySchnorrSecp256k1Signature
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/verifySchnorrSecp256k1Signature`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.VerifySchnorrSecp256k1Signature where

open import Conformance.Eval
```

## long-key

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/long-key
test-long-key : Untyped
test-long-key = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH\SOH")))) (UCon (tagCon bytestring (mkByteString "\CAN\182\190\192\151")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))

expected-long-key : Result
expected-long-key = failure

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-long-key : Set
pending-long-key = Pending (evalRaw test-long-key ≡ expected-long-key)
```

## long-sig

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/long-sig
test-long-sig : Untyped
test-long-sig = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\CAN\182\190\192\151")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t\t"))))

expected-long-sig : Result
expected-long-sig = failure

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-long-sig : Set
pending-long-sig = Pending (evalRaw test-long-sig ≡ expected-long-sig)
```

## short-key

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/short-key
test-short-key : Untyped
test-short-key = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_")))) (UCon (tagCon bytestring (mkByteString "\CAN\182\190\192\151")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))

expected-short-key : Result
expected-short-key = failure

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-short-key : Set
pending-short-key = Pending (evalRaw test-short-key ≡ expected-short-key)
```

## short-sig

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/short-sig
test-short-sig : Untyped
test-short-sig = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\CAN\182\190\192\151")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|"))))

expected-short-sig : Result
expected-short-sig = failure

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-short-sig : Set
pending-short-sig = Pending (evalRaw test-short-sig ≡ expected-short-sig)
```

## test-vector-00

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-00
-- Test vector 0 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
test-test-vector-00 : Untyped
test-test-vector-00 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\249\&0\138\SOH\146X\195\DLEI4O\133\248\157R)\181\&1\200E\131o\153\176\134\SOH\241\DC3\188\224\&6\249")))) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))) (UCon (tagCon bytestring (mkByteString "\233\a\131\US\128\132\141\DLEi\165\&7\ESC@$\DLE6K\223\FS_\131\a\176\bLU\241\206-\202\130\NAK%\246jJ\133\234\139q\228\130\167O8-,\229\235\238\232\253\178\ETB/G}\244\144\r1\ENQ6\192"))))

expected-test-vector-00 : Result
expected-test-vector-00 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-00 : Set
pending-test-vector-00 = Pending (evalRaw test-test-vector-00 ≡ expected-test-vector-00)
```

## test-vector-01

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-01
-- Test vector 1 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
test-test-vector-01 : Untyped
test-test-vector-01 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\223\241\215\DEL*g\FS_6\CAN7&\219#A\190X\254\174\GS\162\222\206\216C$\SI{P+\166Y")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "h\150\189`\238\174)m\180\138\"\159\247\GS\254\a\ESC\222A>mC\249\ETB\220\141\207\140x\222\&3A\137\ACK\209\SUB\201v\171\204\178\v\t\DC2\146\191\244\234\137~\252\182\&9\234\135\FS\250\149\246\222\&3\158K\n"))))

expected-test-vector-01 : Result
expected-test-vector-01 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-01 : Set
pending-test-vector-01 = Pending (evalRaw test-test-vector-01 ≡ expected-test-vector-01)
```

## test-vector-02

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-02
-- Test vector 2 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
test-test-vector-02 : Untyped
test-test-vector-02 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\221\&0\138\254\197w~\DC3\DC2\US\167+\156\193\183\204\SOH9qS\t\176\134\201`\225\143\217iwN\184")))) (UCon (tagCon bytestring (mkByteString "~-X\216\179\188\223\SUB\186\222\199\130\144T\249\r\218\152\ENQ\170\181lw30$\185\208\165\b\183\\")))) (UCon (tagCon bytestring (mkByteString "X1\170\238\215\180K\183N^\171\148\186\157B\148\196\155\207*`r\141\139L \SIP\221\&1<\ESC\171tXy\165\173\149Jr\196Z\145\195\165\GS<z\222\169\141\130\248H\RS\SO\RS\ETXgJo?\183"))))

expected-test-vector-02 : Result
expected-test-vector-02 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-02 : Set
pending-test-vector-02 = Pending (evalRaw test-test-vector-02 ≡ expected-test-vector-02)
```

## test-vector-03

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-03
-- Test vector 3 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (test fails if msg is reduced modulo p or n)
test-test-vector-03 : Untyped
test-test-vector-03 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "%\209\223\249Q\ENQ\245%<@\"\246(\169\150\173:\r\149\251\242\GSF\138\ESC3\248\193`\216\245\ETB")))) (UCon (tagCon bytestring (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255")))) (UCon (tagCon bytestring (mkByteString "~\176P\151W\226F\241\148I\136VQa\FS\185e\236\193\161\135\221Q\182O\218\RS\220\150\&7\213\236\151X+\156\177=\179\147\&7\ENQ\179+\169\130\175Z\242_\215\136\129\235\179'q\252Y\"\239\198n\163"))))

expected-test-vector-03 : Result
expected-test-vector-03 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-03 : Set
pending-test-vector-03 = Pending (evalRaw test-test-vector-03 ≡ expected-test-vector-03)
```

## test-vector-04

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-04
-- Test vector 4 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
test-test-vector-04 : Untyped
test-test-vector-04 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\214\156\&5\t\187\153\228\DC2\230\139\SI\232TNr\131}\250\&0tm\139\226\170e\151_)\210-\199\185")))) (UCon (tagCon bytestring (mkByteString "M\243\195\246\143\204\131\178~\157B\201\EOT1\167$\153\241xu\200\SUBY\155Vl\152\137\185ig\ETX")))) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL;x\206V?\137\160\237\148\DC4\245\170(\173\r\150\214y_\156cv\175\177T\138\246\ETX\179\235E\201\248 }\238\DLE`\203q\192N\128\245\147\ACK\v\a\210\131\b\215\244"))))

expected-test-vector-04 : Result
expected-test-vector-04 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-04 : Set
pending-test-vector-04 = Pending (evalRaw test-test-vector-04 ≡ expected-test-vector-04)
```

## test-vector-05

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-05
-- Test vector 5 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect failure (public key not on the curve)
test-test-vector-05 : Untyped
test-test-vector-05 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\238\253\234L\219gwP\164 \254\232\a\234\207!\235\152\152\174y\185v\135f\228\250\160J-J4")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "l\255\\;\168li\234Ksv\243\SUB\155\203Ot\193\151`\137\178\217\150=\162\229T>\ETBwii\232\155LUd\208\ETXI\DLEk\132\151x]\215\209\215\DC3\168\174\130\179/\167\157_\DEL\196\a\211\155"))))

expected-test-vector-05 : Result
expected-test-vector-05 = failure

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-05 : Set
pending-test-vector-05 = Pending (evalRaw test-test-vector-05 ≡ expected-test-vector-05)
```

## test-vector-06

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-06
-- Test vector 6 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (has_even_y(R) is false)
test-test-vector-06 : Untyped
test-test-vector-06 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\223\241\215\DEL*g\FS_6\CAN7&\219#A\190X\254\174\GS\162\222\206\216C$\SI{P+\166Y")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "\255\249{\213u^\238\164 E:\DC45R5\211\130\246G/\133h\161\139/\ENQz\DC4`)uV<\194yDd\n\198\a\205\DLEz\225\t#\217\239zs\198C\225f\190^\190\175\163K\SUB\197S\226"))))

expected-test-vector-06 : Result
expected-test-vector-06 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-06 : Set
pending-test-vector-06 = Pending (evalRaw test-test-vector-06 ≡ expected-test-vector-06)
```

## test-vector-07

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-07
-- Test vector 7 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (negated message)
test-test-vector-07 : Untyped
test-test-vector-07 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\223\241\215\DEL*g\FS_6\CAN7&\219#A\190X\254\174\GS\162\222\206\216C$\SI{P+\166Y")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "\US\166.3\RS\219\194\FS9G\146\210\171\DC1\NUL\167\180\&2\176\DC3\223?o\244\249\159\203\&3\224\225Q_(\137\v>\219nq\137\182\&0D\139Q\\\228\248b*\149L\254TW5\170\234Q4\252\205\178\189"))))

expected-test-vector-07 : Result
expected-test-vector-07 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-07 : Set
pending-test-vector-07 = Pending (evalRaw test-test-vector-07 ≡ expected-test-vector-07)
```

## test-vector-08

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-08
-- Test vector 8 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (negated s value)
test-test-vector-08 : Untyped
test-test-vector-08 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\223\241\215\DEL*g\FS_6\CAN7&\219#A\190X\254\174\GS\162\222\206\216C$\SI{P+\166Y")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "l\255\\;\168li\234Ksv\243\SUB\155\203Ot\193\151`\137\178\217\150=\162\229T>\ETBwi\150\ETBd\179\170\155/\252\182\239\148{h\135\162&\232\215\201>\NUL\197\237\f\CAN4\255\r\f.m\166"))))

expected-test-vector-08 : Result
expected-test-vector-08 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-08 : Set
pending-test-vector-08 = Pending (evalRaw test-test-vector-08 ≡ expected-test-vector-08)
```

## test-vector-09

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-09
-- Test vector 9 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False
-- (sG - eP is infinite. Test fails in single verification if has_even_y(inf) is defined as true and x(inf) as 0)
test-test-vector-09 : Untyped
test-test-vector-09 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\223\241\215\DEL*g\FS_6\CAN7&\219#A\190X\254\174\GS\162\222\206\216C$\SI{P+\166Y")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\DC2=\218\131(\175\156#\169L\US\238\207\209#\186O\183\&4v\240\213\148\220\182\\d%\189\CAN`Q"))))

expected-test-vector-09 : Result
expected-test-vector-09 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-09 : Set
pending-test-vector-09 = Pending (evalRaw test-test-vector-09 ≡ expected-test-vector-09)
```

## test-vector-10

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-10
-- Test vector 10 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False
-- (sG - eP is infinite. Test fails in single verification if has_even_y(inf) is defined as true and x(inf) as 1)
test-test-vector-10 : Untyped
test-test-vector-10 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\223\241\215\DEL*g\FS_6\CAN7&\219#A\190X\254\174\GS\162\222\206\216C$\SI{P+\166Y")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\SOHv\NAK\251\175Z\226\136d\SOH<\t\151B\222\173\180\219\168\DEL\DC1\172gT\249\&7\128\213\161\131|\241\151"))))

expected-test-vector-10 : Result
expected-test-vector-10 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-10 : Set
pending-test-vector-10 = Pending (evalRaw test-test-vector-10 ≡ expected-test-vector-10)
```

## test-vector-11

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-11
-- Test vector 11 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (sig[0:32] is not an X coordinate on the curve)
test-test-vector-11 : Untyped
test-test-vector-11 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\223\241\215\DEL*g\FS_6\CAN7&\219#A\190X\254\174\GS\162\222\206\216C$\SI{P+\166Y")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "J)\141\172\174W9Z\NAK\208y]\219\253\GS\203VM\168+\SI&\155\199\nt\248\"\EOT)\186\GSi\232\155LUd\208\ETXI\DLEk\132\151x]\215\209\215\DC3\168\174\130\179/\167\157_\DEL\196\a\211\155"))))

expected-test-vector-11 : Result
expected-test-vector-11 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-11 : Set
pending-test-vector-11 = Pending (evalRaw test-test-vector-11 ≡ expected-test-vector-11)
```

## test-vector-12

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-12
-- Test vector 12 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (sig[0:32] is equal to field size)
test-test-vector-12 : Untyped
test-test-vector-12 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\223\241\215\DEL*g\FS_6\CAN7&\219#A\190X\254\174\GS\162\222\206\216C$\SI{P+\166Y")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\254\255\255\252/i\232\155LUd\208\ETXI\DLEk\132\151x]\215\209\215\DC3\168\174\130\179/\167\157_\DEL\196\a\211\155"))))

expected-test-vector-12 : Result
expected-test-vector-12 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-12 : Set
pending-test-vector-12 = Pending (evalRaw test-test-vector-12 ≡ expected-test-vector-12)
```

## test-vector-13

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-13
-- Test vector 13 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (sig[32:64] is equal to curve order)
test-test-vector-13 : Untyped
test-test-vector-13 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\223\241\215\DEL*g\FS_6\CAN7&\219#A\190X\254\174\GS\162\222\206\216C$\SI{P+\166Y")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "l\255\\;\168li\234Ksv\243\SUB\155\203Ot\193\151`\137\178\217\150=\162\229T>\ETBwi\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\254\186\174\220\230\175H\160;\191\210^\140\208\&6AA"))))

expected-test-vector-13 : Result
expected-test-vector-13 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-13 : Set
pending-test-vector-13 = Pending (evalRaw test-test-vector-13 ≡ expected-test-vector-13)
```

## test-vector-14

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-14
-- Test vector 14 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect failure (public key is not a valid X coordinate because it exceeds the field size)
test-test-vector-14 : Untyped
test-test-vector-14 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\254\255\255\252\&0")))) (UCon (tagCon bytestring (mkByteString "$?j\136\133\163\b\211\DC3\EM\138.\ETXpsD\164\t8\")\159\&1\208\b.\250\152\236Nl\137")))) (UCon (tagCon bytestring (mkByteString "l\255\\;\168li\234Ksv\243\SUB\155\203Ot\193\151`\137\178\217\150=\162\229T>\ETBwii\232\155LUd\208\ETXI\DLEk\132\151x]\215\209\215\DC3\168\174\130\179/\167\157_\DEL\196\a\211\155"))))

expected-test-vector-14 : Result
expected-test-vector-14 = failure

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-14 : Set
pending-test-vector-14 = Pending (evalRaw test-test-vector-14 ≡ expected-test-vector-14)
```

## test-vector-15

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-15
-- Test vector 15 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 0)
test-test-vector-15 : Untyped
test-test-vector-15 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "w\140\170S\180\&9:\196gwM\tIz\135\"K\249\250\182\246\230\139#\bd\151\&2Mo\209\ETB")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "qS]\177e\236\217\251\188\EOTn_\250\234a\CANk\182\173Cg2\252\204%)\SUBU\137Td\207`i\206&\191\ETXFb(\241\154:b\219\138d\159-V\SI\172e('\209\175\ENQt\228'\171c"))))

expected-test-vector-15 : Result
expected-test-vector-15 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-15 : Set
pending-test-vector-15 = Pending (evalRaw test-test-vector-15 ≡ expected-test-vector-15)
```

## test-vector-16

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-16
-- Test vector 16 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 1 (added 2022-12)
test-test-vector-16 : Untyped
test-test-vector-16 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "w\140\170S\180\&9:\196gwM\tIz\135\"K\249\250\182\246\230\139#\bd\151\&2Mo\209\ETB")))) (UCon (tagCon bytestring (mkByteString "\DC1")))) (UCon (tagCon bytestring (mkByteString "\b\162\n\n\254\246A$d\146\&2\224i<X:\177\185\147J\230;L5\DC1\243\174\DC14\198\163\ETX\234\&1s\191\234f\131\189\DLE\US\165\170]\188\EM\150\254|\172\252ZW}3\236\DC4VL\236+\172\191"))))

expected-test-vector-16 : Result
expected-test-vector-16 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-16 : Set
pending-test-vector-16 = Pending (evalRaw test-test-vector-16 ≡ expected-test-vector-16)
```

## test-vector-17

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-17
-- Test vector 17 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 17)
test-test-vector-17 : Untyped
test-test-vector-17 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "w\140\170S\180\&9:\196gwM\tIz\135\"K\249\250\182\246\230\139#\bd\151\&2Mo\209\ETB")))) (UCon (tagCon bytestring (mkByteString "\SOH\STX\ETX\EOT\ENQ\ACK\a\b\t\n\v\f\r\SO\SI\DLE\DC1")))) (UCon (tagCon bytestring (mkByteString "Q0\243\154@Y\180;\199\202\192\154\EM\236\229+]\134\153\209\167\RS<R\218\154\253\182\181\n\195p\196\164\130\183{\249`\248h\NAK@\226[gq\236\225\229\163\DEL\216\SOZQ\137|Uf\169~\165\165"))))

expected-test-vector-17 : Result
expected-test-vector-17 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-17 : Set
pending-test-vector-17 = Pending (evalRaw test-test-vector-17 ≡ expected-test-vector-17)
```

## test-vector-18

```
-- builtin/semantics/verifySchnorrSecp256k1Signature/test-vector-18
-- Test vector 18 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 100)
test-test-vector-18 : Untyped
test-test-vector-18 = (UApp (UApp (UApp (UBuiltin verifySchnorrSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "w\140\170S\180\&9:\196gwM\tIz\135\"K\249\250\182\246\230\139#\bd\151\&2Mo\209\ETB")))) (UCon (tagCon bytestring (mkByteString "\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153\153")))) (UCon (tagCon bytestring (mkByteString "@;\DC2\176\216UZ4Au\234~\199FVc\ETX2\RS]\191\168\190o\t\SYN5\SYN>\202y\168X^\211\227\ETB\b\a\231\192;r\SI\197L{#\137\DEL\203\160\233\208\180\160h\148\207\210I\242#g"))))

expected-test-vector-18 : Result
expected-test-vector-18 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifySchnorrSecp256k1Signature`.
pending-test-vector-18 : Set
pending-test-vector-18 = Pending (evalRaw test-test-vector-18 ≡ expected-test-vector-18)
```
