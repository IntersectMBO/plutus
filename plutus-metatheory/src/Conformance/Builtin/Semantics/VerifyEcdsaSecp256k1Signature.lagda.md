---
title: Conformance.Builtin.Semantics.VerifyEcdsaSecp256k1Signature
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/verifyEcdsaSecp256k1Signature`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.VerifyEcdsaSecp256k1Signature where

open import Conformance.Eval
```

## invalid-key

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/invalid-key
-- the header of public key should be 02 or 03
-- 04 is for uncompressed, we don't have uncompressed
-- other bits would also break, e.g. 01,05...
test-invalid-key : Untyped
test-invalid-key = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\EOT\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))

expected-invalid-key : Result
expected-invalid-key = failure

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
pending-invalid-key : Set
pending-invalid-key = Pending (evalRaw test-invalid-key ≡ expected-invalid-key)
```

## long-key

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/long-key
test-long-key : Untyped
test-long-key = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))

expected-long-key : Result
expected-long-key = failure

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
pending-long-key : Set
pending-long-key = Pending (evalRaw test-long-key ≡ expected-long-key)
```

## long-msg

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/long-msg
test-long-msg : Untyped
test-long-msg = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))

expected-long-msg : Result
expected-long-msg = failure

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
pending-long-msg : Set
pending-long-msg = Pending (evalRaw test-long-msg ≡ expected-long-msg)
```

## long-sig

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/long-sig
test-long-sig : Untyped
test-long-sig = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t\t"))))

expected-long-sig : Result
expected-long-sig = failure

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
pending-long-sig : Set
pending-long-sig = Pending (evalRaw test-long-sig ≡ expected-long-sig)
```

## short-key

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/short-key
test-short-key : Untyped
test-short-key = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))

expected-short-key : Result
expected-short-key = failure

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
pending-short-key : Set
pending-short-key = Pending (evalRaw test-short-key ≡ expected-short-key)
```

## short-msg

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/short-msg
test-short-msg : Untyped
test-short-msg = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))

expected-short-msg : Result
expected-short-msg = failure

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
pending-short-msg : Set
pending-short-msg = Pending (evalRaw test-short-msg ≡ expected-short-msg)
```

## short-sig

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/short-sig
test-short-sig : Untyped
test-short-sig = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|"))))

expected-short-sig : Result
expected-short-sig = failure

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
pending-short-sig : Set
pending-short-sig = Pending (evalRaw test-short-sig ≡ expected-short-sig)
```

## test-vector-01

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-01
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Low r, low s signature
-- Expect True
test-test-vector-01 : Untyped
test-test-vector-01 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))

expected-test-vector-01 : Result
expected-test-vector-01 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-01 : Set
pending-test-vector-01 = Pending (evalRaw test-test-vector-01 ≡ expected-test-vector-01)
```

## test-vector-02

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-02
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair and message as test-vector-01, alternative signature (high r, low s)
-- Expect True
test-test-vector-02 : Untyped
test-test-vector-02 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\204\253\138G\129\180\214\145!rr\"\240b\210\199~\151In\FSp\GS:\n\189\132\STX\a\230\220\209\SOHl\SO\227\217/\RS\236\FS\163\&5\236>\178\133a/\184.\226\193\209\248\SOpk.\144}\198\f\196"))))

expected-test-vector-02 : Result
expected-test-vector-02 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-02 : Set
pending-test-vector-02 = Pending (evalRaw test-test-vector-02 ≡ expected-test-vector-02)
```

## test-vector-03

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-03
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair and message as test-vector-01, alternative signature (low r, high s)
-- Expect False (we don't accept signatures with high s components)
test-test-vector-03 : Untyped
test-test-vector-03 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "`>n{\246qR\CAN\130\EOT\247obt\211\140G{\219\195\149L\218\164NN\244\150\145\165\ETB\222\213\234\173\&0\194\230\158>\155\DC2K\204H\250\SOM\n\160\223\219L\169\213\&7\234\GS\205F\201K\143V"))))

expected-test-vector-03 : Result
expected-test-vector-03 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-03 : Set
pending-test-vector-03 = Pending (evalRaw test-test-vector-03 ≡ expected-test-vector-03)
```

## test-vector-04

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-04
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair and message as test-vector-01, low-s version of signature in test-vector-03
-- Expect True
test-test-vector-04 : Untyped
test-test-vector-04 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "`>n{\246qR\CAN\130\EOT\247obt\211\140G{\219\195\149L\218\164NN\244\150\145\165\ETB\222*\NAKR\207=\EMa\193d\237\180\&3\183\ENQ\241\177\176\r\253\vb\158\203\ETX\213\180\145F\ACK\234\177\235"))))

expected-test-vector-04 : Result
expected-test-vector-04 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-04 : Set
pending-test-vector-04 = Pending (evalRaw test-test-vector-04 ≡ expected-test-vector-04)
```

## test-vector-05

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-05
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair and message as test-vector-01, sha3_256 instead of sha2_256
-- Expect True
test-test-vector-05 : Untyped
test-test-vector-05 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "YX\254q\180I\132F\222W\208Aj\184\196\DC1U\252\SYN\212hD\251\195\252\152\152\191\202k\173\249w}\SOH\197\183K\NUL&x\191\233\EOT\233A\192\150\181\250\246\DC3\163{MQ\142\f\167P\171\207\160 "))))

expected-test-vector-05 : Result
expected-test-vector-05 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha3-256`.
pending-test-vector-05 : Set
pending-test-vector-05 = Pending (evalRaw test-test-vector-05 ≡ expected-test-vector-05)
```

## test-vector-06

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-06
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair and message as test-vector-01, sha3_256 instead of sha2_256, alternative signature
-- Expect True
test-test-vector-06 : Untyped
test-test-vector-06 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\215\bo\157P\199\187\221s\156\SYN\218}\SYN\187\171\255[X\252\152 \DC3\201\186\198\223zr\NUL\227\254Il8\239\STX\\:\223\FS\208`\224\167A\DC2X\r\157\"&!=~p\240\238\231&\196\132\233\134"))))

expected-test-vector-06 : Result
expected-test-vector-06 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha3-256`.
pending-test-vector-06 : Set
pending-test-vector-06 = Pending (evalRaw test-test-vector-06 ≡ expected-test-vector-06)
```

## test-vector-07

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-07
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair and signature as test-vector-01, different message
-- Expect False
test-test-vector-07 : Untyped
test-test-vector-07 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "Hello!\n"))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))

expected-test-vector-07 : Result
expected-test-vector-07 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-07 : Set
pending-test-vector-07 = Pending (evalRaw test-test-vector-07 ≡ expected-test-vector-07)
```

## test-vector-08

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-08
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair as test-vector-01, different message with correct signature
-- Expect True
test-test-vector-08 : Untyped
test-test-vector-08 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "Hello!\n"))))) (UCon (tagCon bytestring (mkByteString "4\153\184A\172n\235\&0\v\r\201\237P\233\193\150\210\183O\ETBET\SI\DC2\v\246\ETX\196\129\137\176\238lH\234\204\EOT\242\195\211\t_\161~\DC1\204;vB3\EMc\213*\145w\208\208h\\K?\241\DEL"))))

expected-test-vector-08 : Result
expected-test-vector-08 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-08 : Set
pending-test-vector-08 = Pending (evalRaw test-test-vector-08 ≡ expected-test-vector-08)
```

## test-vector-09

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-09
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair as test-vector-01, different message with alternative correct signature
-- Expect True
test-test-vector-09 : Untyped
test-test-vector-09 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "Hello!\n"))))) (UCon (tagCon bytestring (mkByteString "\252s\210\DEL0\139\176\215p\219\136yN&\148\207\229\219FGd\170\168\188\188\175\199\195\202\219\158W$O\SOH\242\160V\207SE9n\140#\137r\213\&6\228\198{\170s\135\146]~\STX\143!\146\245\217"))))

expected-test-vector-09 : Result
expected-test-vector-09 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-09 : Set
pending-test-vector-09 = Pending (evalRaw test-test-vector-09 ≡ expected-test-vector-09)
```

## test-vector-10

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-10
-- Generated using OpenSSL 3.0.14.4
-- Signing key 144c76f7eaa087f00a0381d0b7d6ec59eac07d4ac21b58695c1118b10127d821
-- Same message and signature as test-vector-01, different signing key
-- Expect False
test-test-vector-10 : Untyped
test-test-vector-10 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX\ETB=;\155\150C\SOH\164\145\155\227#W\RSd0\EM\EOT \154\&2c\FS\204v\180+\137\211\140bt")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))

expected-test-vector-10 : Result
expected-test-vector-10 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-10 : Set
pending-test-vector-10 = Pending (evalRaw test-test-vector-10 ≡ expected-test-vector-10)
```

## test-vector-11

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-11
-- Generated using OpenSSL 3.0.14.4
-- Signing key 144c76f7eaa087f00a0381d0b7d6ec59eac07d4ac21b58695c1118b10127d821
-- Same message as test-vector-01, different keypair with correct signature
-- Expect True
test-test-vector-11 : Untyped
test-test-vector-11 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX\ETB=;\155\150C\SOH\164\145\155\227#W\RSd0\EM\EOT \154\&2c\FS\204v\180+\137\211\140bt")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\164\SO\129\&2\146<\160B\209Y\245\251\167\210\130\138y\220!\"Y\DC2\SUB;\254cD[\243\246 \254\ESC3!_L\169\235]A\235\142\131\EOT\221\192fb6\243\129\243\168\143T\205gt\bG\233\ESCA"))))

expected-test-vector-11 : Result
expected-test-vector-11 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-11 : Set
pending-test-vector-11 = Pending (evalRaw test-test-vector-11 ≡ expected-test-vector-11)
```

## test-vector-12

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-12
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair as test-vector-01, large message with correct signature
-- Expect True
test-test-vector-12 : Untyped
test-test-vector-12 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "Ganga was sunken, and the limp leaves\nWaited for rain, while the black clouds\nGathered far distant, over Himavant.\nThe jungle crouched, humped in silence.\nThen spoke the thunder\nDA\nDatta: what have we given?\nMy friend, blood shaking my heart\nThe awful daring of a moment\226\128\153s surrender\nWhich an age of prudence can never retract\nBy this, and this only, we have existed\nWhich is not to be found in our obituaries\nOr in memories draped by the beneficent spider\nOr under seals broken by the lean solicitor\nIn our empty rooms\nDA\nDayadhvam: I have heard the key\nTurn in the door once and turn once only\nWe think of the key, each in his prison\nThinking of the key, each confirms a prison\nOnly at nightfall, aetherial rumours\nRevive for a moment a broken Coriolanus\nDA\nDamyata: The boat responded\nGaily, to the hand expert with sail and oar\nThe sea was calm, your heart would have responded\nGaily, when invited, beating obedient\nTo controlling hands\n\n                        I sat upon the shore\nFishing, with the arid plain behind me\nShall I at least set my lands in order?\nLondon Bridge is falling down falling down falling down\nPoi s\226\128\153ascose nel foco che gli affina\nQuando fiam ceu chelidon \226\128\148 O swallow swallow\nLe Prince d\226\128\153Aquitaine \195\160 la tour abolie\nThese fragments I have shored against my ruins\nWhy then Ile fit you. Hieronymo\226\128\153s mad againe.\nDatta. Dayadhvam. Damyata.\n                           Shantih    shantih    shantih\n"))))) (UCon (tagCon bytestring (mkByteString "\219\US\fx\RS-if\ENQ%\198\245\STX\211\140\131\194\198,p\EOT\226m\139\134\r\201\168\FS\173\179\183/./\239M4\185\200iuH4\230\199\133\150+?\208\205\210\"\244{\SUB\US/3\136\242l\144"))))

expected-test-vector-12 : Result
expected-test-vector-12 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-12 : Set
pending-test-vector-12 = Pending (evalRaw test-test-vector-12 ≡ expected-test-vector-12)
```

## test-vector-13

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-13
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Random message, same signature as test-vector-01
-- Expect False
test-test-vector-13 : Untyped
test-test-vector-13 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UCon (tagCon bytestring (mkByteString "7z}~\DELI$J\182\ETB\180)\236;kvC&\134\130\&6\171\207\237#\148'\131G\130\171\219")))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))

expected-test-vector-13 : Result
expected-test-vector-13 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
pending-test-vector-13 : Set
pending-test-vector-13 = Pending (evalRaw test-test-vector-13 ≡ expected-test-vector-13)
```

## test-vector-14

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-14
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same as test-vector-01, one bit changed in signature
-- Expect False
test-test-vector-14 : Untyped
test-test-vector-14 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\162\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))

expected-test-vector-14 : Result
expected-test-vector-14 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-14 : Set
pending-test-vector-14 = Pending (evalRaw test-test-vector-14 ≡ expected-test-vector-14)
```

## test-vector-15

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-15
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same as test-vector-01, one bit changed in verification key
-- Expect False
test-test-vector-15 : Untyped
test-test-vector-15 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\RS\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))

expected-test-vector-15 : Result
expected-test-vector-15 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-15 : Set
pending-test-vector-15 = Pending (evalRaw test-test-vector-15 ≡ expected-test-vector-15)
```

## test-vector-16

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-16
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same as test-vector-01, but verification key adjusted to be off the curve.
-- Expect error
test-test-vector-16 : Untyped
test-test-vector-16 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251a")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))

expected-test-vector-16 : Result
expected-test-vector-16 = failure

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-16 : Set
pending-test-vector-16 = Pending (evalRaw test-test-vector-16 ≡ expected-test-vector-16)
```

## test-vector-17

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-17
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same as test-vector-01, but with the r component of the signature adjusted to
-- be out of range (equal to the group order): one less -> False, not error
-- Expect error
test-test-vector-17 : Untyped
test-test-vector-17 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\254\186\174\220\230\175H\160;\191\210^\140\208\&6AA:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))

expected-test-vector-17 : Result
expected-test-vector-17 = failure

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-17 : Set
pending-test-vector-17 = Pending (evalRaw test-test-vector-17 ≡ expected-test-vector-17)
```

## test-vector-18

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/test-vector-18
-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same as test-vector-01, but with the s component of the signature adjusted to
-- be out of range (equal to the group order): one less -> False, not error
-- Expect error
test-test-vector-18 : Untyped
test-test-vector-18 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\254\186\174\220\230\175H\160;\191\210^\140\208\&6AA"))))

expected-test-vector-18 : Result
expected-test-vector-18 = failure

-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
pending-test-vector-18 : Set
pending-test-vector-18 = Pending (evalRaw test-test-vector-18 ≡ expected-test-vector-18)
```
