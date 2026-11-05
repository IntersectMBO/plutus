---
title: Conformance.Builtin.Semantics.VerifyEcdsaSecp256k1Signature
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
<<<<<<< HEAD
test-invalid-key = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "04e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))
=======
test-invalid-key = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\EOT\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))
>>>>>>> origin/master

expected-invalid-key : Result
expected-invalid-key = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
>>>>>>> origin/master
pending-invalid-key : Set
pending-invalid-key = Pending (evalRaw test-invalid-key ≡ expected-invalid-key)
```

## long-key

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/long-key
test-long-key : Untyped
<<<<<<< HEAD
test-long-key = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "02e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f0101")))) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))
=======
test-long-key = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))
>>>>>>> origin/master

expected-long-key : Result
expected-long-key = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
>>>>>>> origin/master
pending-long-key : Set
pending-long-key = Pending (evalRaw test-long-key ≡ expected-long-key)
```

## long-msg

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/long-msg
test-long-msg : Untyped
<<<<<<< HEAD
test-long-msg = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "02e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f0101")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))
=======
test-long-msg = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))
>>>>>>> origin/master

expected-long-msg : Result
expected-long-msg = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
>>>>>>> origin/master
pending-long-msg : Set
pending-long-msg = Pending (evalRaw test-long-msg ≡ expected-long-msg)
```

## long-sig

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/long-sig
test-long-sig : Untyped
<<<<<<< HEAD
test-long-sig = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "02e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c0909"))))
=======
test-long-sig = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t\t"))))
>>>>>>> origin/master

expected-long-sig : Result
expected-long-sig = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
>>>>>>> origin/master
pending-long-sig : Set
pending-long-sig = Pending (evalRaw test-long-sig ≡ expected-long-sig)
```

## short-key

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/short-key
test-short-key : Untyped
<<<<<<< HEAD
test-short-key = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "02e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f")))) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))
=======
test-short-key = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))
>>>>>>> origin/master

expected-short-key : Result
expected-short-key = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
>>>>>>> origin/master
pending-short-key : Set
pending-short-key = Pending (evalRaw test-short-key ≡ expected-short-key)
```

## short-msg

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/short-msg
test-short-msg : Untyped
<<<<<<< HEAD
test-short-msg = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "02e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))
=======
test-short-msg = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))
>>>>>>> origin/master

expected-short-msg : Result
expected-short-msg = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
>>>>>>> origin/master
pending-short-msg : Set
pending-short-msg = Pending (evalRaw test-short-msg ≡ expected-short-msg)
```

## short-sig

```
-- builtin/semantics/verifyEcdsaSecp256k1Signature/short-sig
test-short-sig : Untyped
<<<<<<< HEAD
test-short-sig = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "02e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c"))))
=======
test-short-sig = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\STX\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|"))))
>>>>>>> origin/master

expected-short-sig : Result
expected-short-sig = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-01 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c63a2f3e7b5f509294a4c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a"))))
=======
test-test-vector-01 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))
>>>>>>> origin/master

expected-test-vector-01 : Result
expected-test-vector-01 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-02 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "ccfd8a4781b4d69121727222f062d2c77e97496e1c701d3a0abd840207e6dcd1016c0ee3d92f1eec1ca335ec3eb285612fb82ee2c1d1f80e706b2e907dc60cc4"))))
=======
test-test-vector-02 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\204\253\138G\129\180\214\145!rr\"\240b\210\199~\151In\FSp\GS:\n\189\132\STX\a\230\220\209\SOHl\SO\227\217/\RS\236\FS\163\&5\236>\178\133a/\184.\226\193\209\248\SOpk.\144}\198\f\196"))))
>>>>>>> origin/master

expected-test-vector-02 : Result
expected-test-vector-02 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-03 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "603e6e7bf67152188204f76f6274d38c477bdbc3954cdaa44e4ef49691a517ded5eaad30c2e69e3e9b124bcc48fa0e4d0aa0dfdb4ca9d537ea1dcd46c94b8f56"))))
=======
test-test-vector-03 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "`>n{\246qR\CAN\130\EOT\247obt\211\140G{\219\195\149L\218\164NN\244\150\145\165\ETB\222\213\234\173\&0\194\230\158>\155\DC2K\204H\250\SOM\n\160\223\219L\169\213\&7\234\GS\205F\201K\143V"))))
>>>>>>> origin/master

expected-test-vector-03 : Result
expected-test-vector-03 = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-04 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "603e6e7bf67152188204f76f6274d38c477bdbc3954cdaa44e4ef49691a517de2a1552cf3d1961c164edb433b705f1b1b00dfd0b629ecb03d5b4914606eab1eb"))))
=======
test-test-vector-04 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "`>n{\246qR\CAN\130\EOT\247obt\211\140G{\219\195\149L\218\164NN\244\150\145\165\ETB\222*\NAKR\207=\EMa\193d\237\180\&3\183\ENQ\241\177\176\r\253\vb\158\203\ETX\213\180\145F\ACK\234\177\235"))))
>>>>>>> origin/master

expected-test-vector-04 : Result
expected-test-vector-04 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-05 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "5958fe71b4498446de57d0416ab8c41155fc16d46844fbc3fc9898bfca6badf9777d01c5b74b002678bfe904e941c096b5faf613a37b4d518e0ca750abcfa020"))))
=======
test-test-vector-05 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "YX\254q\180I\132F\222W\208Aj\184\196\DC1U\252\SYN\212hD\251\195\252\152\152\191\202k\173\249w}\SOH\197\183K\NUL&x\191\233\EOT\233A\192\150\181\250\246\DC3\163{MQ\142\f\167P\171\207\160 "))))
>>>>>>> origin/master

expected-test-vector-05 : Result
expected-test-vector-05 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha3-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha3-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-06 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "d7086f9d50c7bbdd739c16da7d16bbabff5b58fc982013c9bac6df7a7200e3fe496c38ef025c3adf1cd060e0a74112580d9d2226213d7e70f0eee726c484e986"))))
=======
test-test-vector-06 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\215\bo\157P\199\187\221s\156\SYN\218}\SYN\187\171\255[X\252\152 \DC3\201\186\198\223zr\NUL\227\254Il8\239\STX\\:\223\FS\208`\224\167A\DC2X\r\157\"&!=~p\240\238\231&\196\132\233\134"))))
>>>>>>> origin/master

expected-test-vector-06 : Result
expected-test-vector-06 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha3-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha3-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-07 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "48656c6c6f210a"))))) (UCon (tagCon bytestring (mkByteString "4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c63a2f3e7b5f509294a4c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a"))))
=======
test-test-vector-07 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "Hello!\n"))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))
>>>>>>> origin/master

expected-test-vector-07 : Result
expected-test-vector-07 = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-08 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "48656c6c6f210a"))))) (UCon (tagCon bytestring (mkByteString "3499b841ac6eeb300b0dc9ed50e9c196d2b74f1745540f120bf603c48189b0ee6c48eacc04f2c3d3095fa17e11cc3b7642331963d52a9177d0d0685c4b3ff17f"))))
=======
test-test-vector-08 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "Hello!\n"))))) (UCon (tagCon bytestring (mkByteString "4\153\184A\172n\235\&0\v\r\201\237P\233\193\150\210\183O\ETBET\SI\DC2\v\246\ETX\196\129\137\176\238lH\234\204\EOT\242\195\211\t_\161~\DC1\204;vB3\EMc\213*\145w\208\208h\\K?\241\DEL"))))
>>>>>>> origin/master

expected-test-vector-08 : Result
expected-test-vector-08 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-09 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "48656c6c6f210a"))))) (UCon (tagCon bytestring (mkByteString "fc73d27f308bb0d770db88794e2694cfe5db464764aaa8bcbcafc7c3cadb9e57244f01f2a056cf5345396e8c238972d536e4c67baa7387925d7e028f2192f5d9"))))
=======
test-test-vector-09 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "Hello!\n"))))) (UCon (tagCon bytestring (mkByteString "\252s\210\DEL0\139\176\215p\219\136yN&\148\207\229\219FGd\170\168\188\188\175\199\195\202\219\158W$O\SOH\242\160V\207SE9n\140#\137r\213\&6\228\198{\170s\135\146]~\STX\143!\146\245\217"))))
>>>>>>> origin/master

expected-test-vector-09 : Result
expected-test-vector-09 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-10 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "03173d3b9b964301a4919be323571e64301904209a32631ccc76b42b89d38c6274")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c63a2f3e7b5f509294a4c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a"))))
=======
test-test-vector-10 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX\ETB=;\155\150C\SOH\164\145\155\227#W\RSd0\EM\EOT \154\&2c\FS\204v\180+\137\211\140bt")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))
>>>>>>> origin/master

expected-test-vector-10 : Result
expected-test-vector-10 = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-11 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "03173d3b9b964301a4919be323571e64301904209a32631ccc76b42b89d38c6274")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "a40e8132923ca042d159f5fba7d2828a79dc212259121a3bfe63445bf3f620fe1b33215f4ca9eb5d41eb8e8304ddc0666236f381f3a88f54cd67740847e91b41"))))
=======
test-test-vector-11 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX\ETB=;\155\150C\SOH\164\145\155\227#W\RSd0\EM\EOT \154\&2c\FS\204v\180+\137\211\140bt")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\164\SO\129\&2\146<\160B\209Y\245\251\167\210\130\138y\220!\"Y\DC2\SUB;\254cD[\243\246 \254\ESC3!_L\169\235]A\235\142\131\EOT\221\192fb6\243\129\243\168\143T\205gt\bG\233\ESCA"))))
>>>>>>> origin/master

expected-test-vector-11 : Result
expected-test-vector-11 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-12 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "47616e6761207761732073756e6b656e2c20616e6420746865206c696d70206c65617665730a57616974656420666f72207261696e2c207768696c652074686520626c61636b20636c6f7564730a4761746865726564206661722064697374616e742c206f7665722048696d6176616e742e0a546865206a756e676c652063726f75636865642c2068756d70656420696e2073696c656e63652e0a5468656e2073706f6b6520746865207468756e6465720a44410a44617474613a2077686174206861766520776520676976656e3f0a4d7920667269656e642c20626c6f6f64207368616b696e67206d792068656172740a54686520617766756c20646172696e67206f662061206d6f6d656e74e28099732073757272656e6465720a576869636820616e20616765206f662070727564656e63652063616e206e6576657220726574726163740a427920746869732c20616e642074686973206f6e6c792c207765206861766520657869737465640a5768696368206973206e6f7420746f20626520666f756e6420696e206f7572206f6269747561726965730a4f7220696e206d656d6f7269657320647261706564206279207468652062656e65666963656e74207370696465720a4f7220756e646572207365616c732062726f6b656e20627920746865206c65616e20736f6c696369746f720a496e206f757220656d70747920726f6f6d730a44410a44617961646876616d3a2049206861766520686561726420746865206b65790a5475726e20696e2074686520646f6f72206f6e636520616e64207475726e206f6e6365206f6e6c790a5765207468696e6b206f6620746865206b65792c206561636820696e2068697320707269736f6e0a5468696e6b696e67206f6620746865206b65792c206561636820636f6e6669726d73206120707269736f6e0a4f6e6c79206174206e6967687466616c6c2c2061657468657269616c2072756d6f7572730a52657669766520666f722061206d6f6d656e7420612062726f6b656e20436f72696f6c616e75730a44410a44616d796174613a2054686520626f617420726573706f6e6465640a4761696c792c20746f207468652068616e64206578706572742077697468207361696c20616e64206f61720a54686520736561207761732063616c6d2c20796f757220686561727420776f756c64206861766520726573706f6e6465640a4761696c792c207768656e20696e76697465642c2062656174696e67206f62656469656e740a546f20636f6e74726f6c6c696e672068616e64730a0a20202020202020202020202020202020202020202020202049207361742075706f6e207468652073686f72650a46697368696e672c207769746820746865206172696420706c61696e20626568696e64206d650a5368616c6c2049206174206c6561737420736574206d79206c616e647320696e206f726465723f0a4c6f6e646f6e204272696467652069732066616c6c696e6720646f776e2066616c6c696e6720646f776e2066616c6c696e6720646f776e0a506f692073e280996173636f7365206e656c20666f636f2063686520676c6920616666696e610a5175616e646f206669616d20636575206368656c69646f6e20e28094204f207377616c6c6f77207377616c6c6f770a4c65205072696e63652064e28099417175697461696e6520c3a0206c6120746f75722061626f6c69650a546865736520667261676d656e7473204920686176652073686f72656420616761696e7374206d79207275696e730a576879207468656e20496c652066697420796f752e20486965726f6e796d6fe2809973206d616420616761696e652e0a44617474612e2044617961646876616d2e2044616d796174612e0a2020202020202020202020202020202020202020202020202020205368616e746968202020207368616e746968202020207368616e7469680a"))))) (UCon (tagCon bytestring (mkByteString "db1f0c781e2d69660525c6f502d38c83c2c62c7004e26d8b860dc9a81cadb3b72f2e2fef4d34b9c869754834e6c785962b3fd0cdd222f47b1a1f2f3388f26c90"))))
=======
test-test-vector-12 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "Ganga was sunken, and the limp leaves\nWaited for rain, while the black clouds\nGathered far distant, over Himavant.\nThe jungle crouched, humped in silence.\nThen spoke the thunder\nDA\nDatta: what have we given?\nMy friend, blood shaking my heart\nThe awful daring of a moment\226\128\153s surrender\nWhich an age of prudence can never retract\nBy this, and this only, we have existed\nWhich is not to be found in our obituaries\nOr in memories draped by the beneficent spider\nOr under seals broken by the lean solicitor\nIn our empty rooms\nDA\nDayadhvam: I have heard the key\nTurn in the door once and turn once only\nWe think of the key, each in his prison\nThinking of the key, each confirms a prison\nOnly at nightfall, aetherial rumours\nRevive for a moment a broken Coriolanus\nDA\nDamyata: The boat responded\nGaily, to the hand expert with sail and oar\nThe sea was calm, your heart would have responded\nGaily, when invited, beating obedient\nTo controlling hands\n\n                        I sat upon the shore\nFishing, with the arid plain behind me\nShall I at least set my lands in order?\nLondon Bridge is falling down falling down falling down\nPoi s\226\128\153ascose nel foco che gli affina\nQuando fiam ceu chelidon \226\128\148 O swallow swallow\nLe Prince d\226\128\153Aquitaine \195\160 la tour abolie\nThese fragments I have shored against my ruins\nWhy then Ile fit you. Hieronymo\226\128\153s mad againe.\nDatta. Dayadhvam. Damyata.\n                           Shantih    shantih    shantih\n"))))) (UCon (tagCon bytestring (mkByteString "\219\US\fx\RS-if\ENQ%\198\245\STX\211\140\131\194\198,p\EOT\226m\139\134\r\201\168\FS\173\179\183/./\239M4\185\200iuH4\230\199\133\150+?\208\205\210\"\244{\SUB\US/3\136\242l\144"))))
>>>>>>> origin/master

expected-test-vector-12 : Result
expected-test-vector-12 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-13 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UCon (tagCon bytestring (mkByteString "377a7d7e7f49244ab617b429ec3b6b764326868236abcfed239427834782abdb")))) (UCon (tagCon bytestring (mkByteString "4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c63a2f3e7b5f509294a4c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a"))))
=======
test-test-vector-13 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UCon (tagCon bytestring (mkByteString "7z}~\DELI$J\182\ETB\180)\236;kvC&\134\130\&6\171\207\237#\148'\131G\130\171\219")))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))
>>>>>>> origin/master

expected-test-vector-13 : Result
expected-test-vector-13 = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-14 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c63a2f3e7b5f509294a2c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a"))))
=======
test-test-vector-14 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\162\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))
>>>>>>> origin/master

expected-test-vector-14 : Result
expected-test-vector-14 = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-15 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621ecd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c63a2f3e7b5f509294a4c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a"))))
=======
test-test-vector-15 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\RS\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))
>>>>>>> origin/master

expected-test-vector-15 : Result
expected-test-vector-15 = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-16 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb61")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c63a2f3e7b5f509294a4c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a"))))
=======
test-test-vector-16 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251a")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))
>>>>>>> origin/master

expected-test-vector-16 : Result
expected-test-vector-16 = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-17 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd03641413a2f3e7b5f509294a4c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a"))))
=======
test-test-vector-17 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\254\186\174\220\230\175H\160;\191\210^\140\208\&6AA:/>{_P\146\148\164\194\226/\235iz\SYN\183\146\250\191\235\233\208\243\132\ETX\177\201)\131kZ"))))
>>>>>>> origin/master

expected-test-vector-17 : Result
expected-test-vector-17 = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
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
<<<<<<< HEAD
test-test-vector-18 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c6fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"))))
=======
test-test-vector-18 = (UApp (UApp (UApp (UBuiltin verifyEcdsaSecp256k1Signature) (UCon (tagCon bytestring (mkByteString "\ETX.C5\137\220\230\CANc\EM\145q\244\209\227\250\148jX2b\US\205)U\153@\160\149\SI\150\251o")))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString ""))))) (UCon (tagCon bytestring (mkByteString "IA\NAK^#\ETX\152\138\ESC\233z\STX\US\186\249\254`d\208^\166\148\188^\137\&2\143)qT\229\198\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\254\186\174\220\230\175H\160;\191\210^\140\208\&6AA"))))
>>>>>>> origin/master

expected-test-vector-18 : Result
expected-test-vector-18 = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEcdsaSecp256k1Signature`; postulated builtin `sha2-256`.
>>>>>>> origin/master
pending-test-vector-18 : Set
pending-test-vector-18 = Pending (evalRaw test-test-vector-18 ≡ expected-test-vector-18)
```
