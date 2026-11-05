---
title: Conformance.Builtin.Semantics.VerifyEd25519Signature
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
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/verifyEd25519Signature`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.VerifyEd25519Signature where

open import Conformance.Eval
```

## long-key

```
-- builtin/semantics/verifyEd25519Signature/long-key
test-long-key : Untyped
<<<<<<< HEAD
test-long-key = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f0101")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))
=======
test-long-key = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH\SOH")))) (UCon (tagCon bytestring (mkByteString "\CAN\182\190\192\151")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))
>>>>>>> origin/master

expected-long-key : Result
expected-long-key = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-long-key : Set
pending-long-key = Pending (evalRaw test-long-key ≡ expected-long-key)
```

## long-sig

```
-- builtin/semantics/verifyEd25519Signature/long-sig
test-long-sig : Untyped
<<<<<<< HEAD
test-long-sig = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c0909"))))
=======
test-long-sig = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\CAN\182\190\192\151")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t\t"))))
>>>>>>> origin/master

expected-long-sig : Result
expected-long-sig = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-long-sig : Set
pending-long-sig = Pending (evalRaw test-long-sig ≡ expected-long-sig)
```

## short-key

```
-- builtin/semantics/verifyEd25519Signature/short-key
test-short-key : Untyped
<<<<<<< HEAD
test-short-key = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))
=======
test-short-key = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_")))) (UCon (tagCon bytestring (mkByteString "\CAN\182\190\192\151")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))
>>>>>>> origin/master

expected-short-key : Result
expected-short-key = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-short-key : Set
pending-short-key = Pending (evalRaw test-short-key ≡ expected-short-key)
```

## short-sig

```
-- builtin/semantics/verifyEd25519Signature/short-sig
test-short-sig : Untyped
<<<<<<< HEAD
test-short-sig = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c"))))
=======
test-short-sig = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\CAN\182\190\192\151")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|"))))
>>>>>>> origin/master

expected-short-sig : Result
expected-short-sig = failure

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-short-sig : Set
pending-short-sig = Pending (evalRaw test-short-sig ≡ expected-short-sig)
```

## test-vector-01

```
-- builtin/semantics/verifyEd25519Signature/test-vector-01
test-test-vector-01 : Untyped
<<<<<<< HEAD
test-test-vector-01 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"))))
=======
test-test-vector-01 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\215Z\152\SOH\130\177\n\183\213K\254\211\201d\a:\SO\225r\243\218\166#%\175\STX\SUBh\247\aQ\SUB")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "\229VC\NUL\195`\172r\144\134\226\204\128n\130\138\132\135\DEL\RS\184\229\217t\216s\224e\"I\SOHU_\184\130\NAK\144\163;\172\198\RS9p\FS\249\180k\210[\245\240Y[\190$eQAC\142z\DLE\v"))))
>>>>>>> origin/master

expected-test-vector-01 : Result
expected-test-vector-01 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-01 : Set
pending-test-vector-01 = Pending (evalRaw test-test-vector-01 ≡ expected-test-vector-01)
```

## test-vector-02

```
-- builtin/semantics/verifyEd25519Signature/test-vector-02
test-test-vector-02 : Untyped
<<<<<<< HEAD
test-test-vector-02 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")))) (UCon (tagCon bytestring (mkByteString "72")))) (UCon (tagCon bytestring (mkByteString "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"))))
=======
test-test-vector-02 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "=@\ETB\195\232C\137Z\146\183\n\167M\ESC~\188\156\152,\207.\196\150\140\192\205U\241*\244f\f")))) (UCon (tagCon bytestring (mkByteString "r")))) (UCon (tagCon bytestring (mkByteString "\146\160\t\169\240\212\202\184r\SO\130\v_d%@\162\178{T\SYNP?\143\179v\"#\235\219i\218\bZ\193\228>\NAK\153nE\143\&6\DC3\208\241\GS\140\&8{.\174\180\&0*\238\176\r)\SYN\DC2\187\f\NUL"))))
>>>>>>> origin/master

expected-test-vector-02 : Result
expected-test-vector-02 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-02 : Set
pending-test-vector-02 = Pending (evalRaw test-test-vector-02 ≡ expected-test-vector-02)
```

## test-vector-03

```
-- builtin/semantics/verifyEd25519Signature/test-vector-03
test-test-vector-03 : Untyped
<<<<<<< HEAD
test-test-vector-03 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025")))) (UCon (tagCon bytestring (mkByteString "af82")))) (UCon (tagCon bytestring (mkByteString "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a"))))
=======
test-test-vector-03 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\252Q\205\142b\CAN\161\163\141\164~\208\STX0\240X\b\SYN\237\DC3\186\&3\ETX\172]\235\145\NAKH\144\128%")))) (UCon (tagCon bytestring (mkByteString "\175\130")))) (UCon (tagCon bytestring (mkByteString "b\145\214W\222\236$\STXH'\230\156:\190\SOH\163\f\229H\162\132t:D^6\128\215\219Z\195\172\CAN\255\155S\141\SYN\242\144\174g\247`\152M\198YJ|\NAK\233qn\210\141\192'\190\206\234\RS\196\n"))))
>>>>>>> origin/master

expected-test-vector-03 : Result
expected-test-vector-03 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-03 : Set
pending-test-vector-03 = Pending (evalRaw test-test-vector-03 ≡ expected-test-vector-03)
```

## test-vector-04

```
-- builtin/semantics/verifyEd25519Signature/test-vector-04
test-test-vector-04 : Untyped
<<<<<<< HEAD
test-test-vector-04 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e61a185bcef2613a6c7cb79763ce945d3b245d76114dd440bcf5f2dc1aa57057")))) (UCon (tagCon bytestring (mkByteString "cbc77b")))) (UCon (tagCon bytestring (mkByteString "d9868d52c2bebce5f3fa5a79891970f309cb6591e3e1702a70276fa97c24b3a8e58606c38c9758529da50ee31b8219cba45271c689afa60b0ea26c99db19b00c"))))
=======
test-test-vector-04 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\230\SUB\CAN[\206\242a:l|\183\151c\206\148];$]v\DC1M\212@\188\245\242\220\SUB\165pW")))) (UCon (tagCon bytestring (mkByteString "\203\199{")))) (UCon (tagCon bytestring (mkByteString "\217\134\141R\194\190\188\229\243\250Zy\137\EMp\243\t\203e\145\227\225p*p'o\169|$\179\168\229\134\ACK\195\140\151XR\157\165\SO\227\ESC\130\EM\203\164Rq\198\137\175\166\v\SO\162l\153\219\EM\176\f"))))
>>>>>>> origin/master

expected-test-vector-04 : Result
expected-test-vector-04 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-04 : Set
pending-test-vector-04 = Pending (evalRaw test-test-vector-04 ≡ expected-test-vector-04)
```

## test-vector-05

```
-- builtin/semantics/verifyEd25519Signature/test-vector-05
test-test-vector-05 : Untyped
<<<<<<< HEAD
test-test-vector-05 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "6df9340c138cc188b5fe4464ebaa3f7fc206a2d55c3434707e74c9fc04e20ebb")))) (UCon (tagCon bytestring (mkByteString "5f4c8989")))) (UCon (tagCon bytestring (mkByteString "124f6fc6b0d100842769e71bd530664d888df8507df6c56dedfdb509aeb93416e26b918d38aa06305df3095697c18b2aa832eaa52edc0ae49fbae5a85e150c07"))))
=======
test-test-vector-05 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "m\249\&4\f\DC3\140\193\136\181\254Dd\235\170?\DEL\194\ACK\162\213\\44p~t\201\252\EOT\226\SO\187")))) (UCon (tagCon bytestring (mkByteString "_L\137\137")))) (UCon (tagCon bytestring (mkByteString "\DC2Oo\198\176\209\NUL\132'i\231\ESC\213\&0fM\136\141\248P}\246\197m\237\253\181\t\174\185\&4\SYN\226k\145\141\&8\170\ACK0]\243\tV\151\193\139*\168\&2\234\165.\220\n\228\159\186\229\168^\NAK\f\a"))))
>>>>>>> origin/master

expected-test-vector-05 : Result
expected-test-vector-05 = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-05 : Set
pending-test-vector-05 = Pending (evalRaw test-test-vector-05 ≡ expected-test-vector-05)
```

## test-vector-06

```
-- builtin/semantics/verifyEd25519Signature/test-vector-06
test-test-vector-06 : Untyped
<<<<<<< HEAD
test-test-vector-06 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01")))) (UCon (tagCon bytestring (mkByteString "18b6bec097")))) (UCon (tagCon bytestring (mkByteString "b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09"))))
=======
test-test-vector-06 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\226S\175\af\128K\134\155\177Y[\233v[SH\134\187\170\184\&0[\245\r\188\DEL\137\155\251_\SOH")))) (UCon (tagCon bytestring (mkByteString "\CAN\182\190\192\151")))) (UCon (tagCon bytestring (mkByteString "\178\252F\173G\175FDx\193\153\225\248\190\SYN\159\ESC\230\&2|\DEL\154\nf\137\&7\FS\169L\175\EOT\ACKJ\SOH\178*\255\NAK \171\213\137Q4\SYN\ETX\250\237v\140\247\140\233z\231\176\&8\171\254Ej\161|\t"))))
>>>>>>> origin/master

expected-test-vector-06 : Result
expected-test-vector-06 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-06 : Set
pending-test-vector-06 = Pending (evalRaw test-test-vector-06 ≡ expected-test-vector-06)
```

## test-vector-07

```
-- builtin/semantics/verifyEd25519Signature/test-vector-07
test-test-vector-07 : Untyped
<<<<<<< HEAD
test-test-vector-07 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "fbcfbfa40505d7f2be444a33d185cc54e16d615260e1640b2b5087b83ee3643d")))) (UCon (tagCon bytestring (mkByteString "89010d855972")))) (UCon (tagCon bytestring (mkByteString "6ed629fc1d9ce9e1468755ff636d5a3f40a5d9c91afd93b79d241830f7e5fa29854b8f20cc6eecbb248dbd8d16d14e99752194e4904d09c74d639518839d2300"))))
=======
test-test-vector-07 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\251\207\191\164\ENQ\ENQ\215\242\190DJ3\209\133\204T\225maR`\225d\v+P\135\184>\227d=")))) (UCon (tagCon bytestring (mkByteString "\137\SOH\r\133Yr")))) (UCon (tagCon bytestring (mkByteString "n\214)\252\GS\156\233\225F\135U\255cmZ?@\165\217\201\SUB\253\147\183\157$\CAN0\247\229\250)\133K\143 \204n\236\187$\141\189\141\SYN\209N\153u!\148\228\144M\t\199Mc\149\CAN\131\157#\NUL"))))
>>>>>>> origin/master

expected-test-vector-07 : Result
expected-test-vector-07 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-07 : Set
pending-test-vector-07 = Pending (evalRaw test-test-vector-07 ≡ expected-test-vector-07)
```

## test-vector-08

```
-- builtin/semantics/verifyEd25519Signature/test-vector-08
test-test-vector-08 : Untyped
<<<<<<< HEAD
test-test-vector-08 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "98a5e3a36e67aaba89888bf093de1ad963e774013b3902bfab356d8b90178a63")))) (UCon (tagCon bytestring (mkByteString "b4a8f381e70e7a")))) (UCon (tagCon bytestring (mkByteString "6e0af2fe55ae377a6b7a7278edfb419bd321e06d0df5e27037db8812e7e3529810fa5552f6c0020985ca17a0e02e036d7b222a24f99b77b75fdd16cb05568107"))))
=======
test-test-vector-08 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\152\165\227\163ng\170\186\137\136\139\240\147\222\SUB\217c\231t\SOH;9\STX\191\171\&5m\139\144\ETB\138c")))) (UCon (tagCon bytestring (mkByteString "\180\168\243\129\231\SOz")))) (UCon (tagCon bytestring (mkByteString "n\n\242\254U\174\&7zkzrx\237\251A\155\211!\224m\r\245\226p7\219\136\DC2\231\227R\152\DLE\250UR\246\192\STX\t\133\202\ETB\160\224.\ETXm{\"*$\249\155w\183_\221\SYN\203\ENQV\129\a"))))
>>>>>>> origin/master

expected-test-vector-08 : Result
expected-test-vector-08 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-08 : Set
pending-test-vector-08 = Pending (evalRaw test-test-vector-08 ≡ expected-test-vector-08)
```

## test-vector-09

```
-- builtin/semantics/verifyEd25519Signature/test-vector-09
test-test-vector-09 : Untyped
<<<<<<< HEAD
test-test-vector-09 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "f81fb54a825fced95eb033afcd64314075abfb0abd20a970892503436f34b863")))) (UCon (tagCon bytestring (mkByteString "4284abc51bb67235")))) (UCon (tagCon bytestring (mkByteString "d6addec5afb0528ac17bb178d3e7f2887f9adbb1ad16e110545ef3bc57f9de2314a5c8388f723b8907be0f3ac90c6259bbe885ecc17645df3db7d488f805fa08"))))
=======
test-test-vector-09 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\248\US\181J\130_\206\217^\176\&3\175\205d1@u\171\251\n\189 \169p\137%\ETXCo4\184c")))) (UCon (tagCon bytestring (mkByteString "B\132\171\197\ESC\182r5")))) (UCon (tagCon bytestring (mkByteString "\214\173\222\197\175\176R\138\193{\177x\211\231\242\136\DEL\154\219\177\173\SYN\225\DLET^\243\188W\249\222#\DC4\165\200\&8\143r;\137\a\190\SI:\201\fbY\187\232\133\236\193vE\223=\183\212\136\248\ENQ\250\b"))))
>>>>>>> origin/master

expected-test-vector-09 : Result
expected-test-vector-09 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-09 : Set
pending-test-vector-09 = Pending (evalRaw test-test-vector-09 ≡ expected-test-vector-09)
```

## test-vector-10

```
-- builtin/semantics/verifyEd25519Signature/test-vector-10
test-test-vector-10 : Untyped
<<<<<<< HEAD
test-test-vector-10 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "c1a49c66e617f9ef5ec66bc4c6564ca33de2a5fb5e1464062e6d6c6219155efd")))) (UCon (tagCon bytestring (mkByteString "672bf8965d04bc5146")))) (UCon (tagCon bytestring (mkByteString "2c76a04af2391c147082e33faacdbe56642a1e134bd388620b852b901a6bc16ff6c9cc9404c41dea12ed281da067a1513866f9d964f8bdd24953856c50042901"))))
=======
test-test-vector-10 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\193\164\156f\230\ETB\249\239^\198k\196\198VL\163=\226\165\251^\DC4d\ACK.mlb\EM\NAK^\253")))) (UCon (tagCon bytestring (mkByteString "g+\248\150]\EOT\188QF")))) (UCon (tagCon bytestring (mkByteString ",v\160J\242\&9\FS\DC4p\130\227?\170\205\190Vd*\RS\DC3K\211\136b\v\133+\144\SUBk\193o\246\201\204\148\EOT\196\GS\234\DC2\237(\GS\160g\161Q8f\249\217d\248\189\210IS\133lP\EOT)\SOH"))))
>>>>>>> origin/master

expected-test-vector-10 : Result
expected-test-vector-10 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-10 : Set
pending-test-vector-10 = Pending (evalRaw test-test-vector-10 ≡ expected-test-vector-10)
```

## test-vector-11

```
-- builtin/semantics/verifyEd25519Signature/test-vector-11
test-test-vector-11 : Untyped
<<<<<<< HEAD
test-test-vector-11 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "31b2524b8348f7ab1dfafa675cc538e9a84e3fe5819e27c12ad8bbc1a36e4dff")))) (UCon (tagCon bytestring (mkByteString "33d7a786aded8c1bf691")))) (UCon (tagCon bytestring (mkByteString "28e4598c415ae9de01f03f9f3fab4e919e8bf537dd2b0cdf6e79b9e6559c9409d9151a4c40f083193937627c369488259e99da5a9f0a87497fa6696a5dd6ce08"))))
=======
test-test-vector-11 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "1\178RK\131H\247\171\GS\250\250g\\\197\&8\233\168N?\229\129\158'\193*\216\187\193\163nM\255")))) (UCon (tagCon bytestring (mkByteString "3\215\167\134\173\237\140\ESC\246\145")))) (UCon (tagCon bytestring (mkByteString "(\228Y\140AZ\233\222\SOH\240?\159?\171N\145\158\139\245\&7\221+\f\223ny\185\230U\156\148\t\217\NAK\SUBL@\240\131\EM97b|6\148\136%\158\153\218Z\159\n\135I\DEL\166ij]\214\206\b"))))
>>>>>>> origin/master

expected-test-vector-11 : Result
expected-test-vector-11 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-11 : Set
pending-test-vector-11 = Pending (evalRaw test-test-vector-11 ≡ expected-test-vector-11)
```

## test-vector-12

```
-- builtin/semantics/verifyEd25519Signature/test-vector-12
test-test-vector-12 : Untyped
<<<<<<< HEAD
test-test-vector-12 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "44b57ee30cdb55829d0a5d4f046baef078f1e97a7f21b62d75f8e96ea139c35f")))) (UCon (tagCon bytestring (mkByteString "3486f68848a65a0eb5507d")))) (UCon (tagCon bytestring (mkByteString "77d389e599630d934076329583cd4105a649a9292abc44cd28c40000c8e2f5ac7660a81c85b72af8452d7d25c070861dae91601c7803d656531650dd4e5c4100"))))
=======
test-test-vector-12 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "D\181~\227\f\219U\130\157\n]O\EOTk\174\240x\241\233z\DEL!\182-u\248\233n\161\&9\195_")))) (UCon (tagCon bytestring (mkByteString "4\134\246\136H\166Z\SO\181P}")))) (UCon (tagCon bytestring (mkByteString "w\211\137\229\153c\r\147@v2\149\131\205A\ENQ\166I\169)*\188D\205(\196\NUL\NUL\200\226\245\172v`\168\FS\133\183*\248E-}%\192p\134\GS\174\145`\FSx\ETX\214VS\SYNP\221N\\A\NUL"))))
>>>>>>> origin/master

expected-test-vector-12 : Result
expected-test-vector-12 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-12 : Set
pending-test-vector-12 = Pending (evalRaw test-test-vector-12 ≡ expected-test-vector-12)
```

## test-vector-13

```
-- builtin/semantics/verifyEd25519Signature/test-vector-13
test-test-vector-13 : Untyped
<<<<<<< HEAD
test-test-vector-13 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "6fe83693d011d111131c4f3fbaaa40a9d3d76b30012ff73bb0e39ec27ab18257")))) (UCon (tagCon bytestring (mkByteString "5a8d9d0a22357e6655f9c785")))) (UCon (tagCon bytestring (mkByteString "0f9ad9793033a2fa06614b277d37381e6d94f65ac2a5a94558d09ed6ce922258c1a567952e863ac94297aec3c0d0c8ddf71084e504860bb6ba27449b55adc40e"))))
=======
test-test-vector-13 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "o\232\&6\147\208\DC1\209\DC1\DC3\FSO?\186\170@\169\211\215k0\SOH/\247;\176\227\158\194z\177\130W")))) (UCon (tagCon bytestring (mkByteString "Z\141\157\n\"5~fU\249\199\133")))) (UCon (tagCon bytestring (mkByteString "\SI\154\217y03\162\250\ACKaK'}78\RSm\148\246Z\194\165\169EX\208\158\214\206\146\"X\193\165g\149.\134:\201B\151\174\195\192\208\200\221\247\DLE\132\229\EOT\134\v\182\186'D\155U\173\196\SO"))))
>>>>>>> origin/master

expected-test-vector-13 : Result
expected-test-vector-13 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-13 : Set
pending-test-vector-13 = Pending (evalRaw test-test-vector-13 ≡ expected-test-vector-13)
```

## test-vector-14

```
-- builtin/semantics/verifyEd25519Signature/test-vector-14
test-test-vector-14 : Untyped
<<<<<<< HEAD
test-test-vector-14 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "a2eb8c0501e30bae0cf842d2bde8dec7386f6b7fc3981b8c57c9792bb94cf2dd")))) (UCon (tagCon bytestring (mkByteString "b87d3813e03f58cf19fd0b6395")))) (UCon (tagCon bytestring (mkByteString "d8bb64aad8c9955a115a793addd24f7f2b077648714f49c4694ec995b330d09d640df310f447fd7b6cb5c14f9fe9f490bcf8cfadbfd2169c8ac20d3b8af49a0c"))))
=======
test-test-vector-14 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\162\235\140\ENQ\SOH\227\v\174\f\248B\210\189\232\222\199\&8ok\DEL\195\152\ESC\140W\201y+\185L\242\221")))) (UCon (tagCon bytestring (mkByteString "\184}8\DC3\224?X\207\EM\253\vc\149")))) (UCon (tagCon bytestring (mkByteString "\216\187d\170\216\201\149Z\DC1Zy:\221\210O\DEL+\avHqOI\196iN\201\149\179\&0\208\157d\r\243\DLE\244G\253{l\181\193O\159\233\244\144\188\248\207\173\191\210\SYN\156\138\194\r;\138\244\154\f"))))
>>>>>>> origin/master

expected-test-vector-14 : Result
expected-test-vector-14 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-14 : Set
pending-test-vector-14 = Pending (evalRaw test-test-vector-14 ≡ expected-test-vector-14)
```

## test-vector-15

```
-- builtin/semantics/verifyEd25519Signature/test-vector-15
test-test-vector-15 : Untyped
<<<<<<< HEAD
test-test-vector-15 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "cf3af898467a5b7a52d33d53bc037e2642a8da996903fc252217e9c033e2f291")))) (UCon (tagCon bytestring (mkByteString "55c7fa434f5ed8cdec2b7aeac173")))) (UCon (tagCon bytestring (mkByteString "6ee3fe81e23c60eb2312b2006b3b25e6838e02106623f844c44edb8dafd66ab0671087fd195df5b8f58a1d6e52af42908053d55c7321010092748795ef94cf06"))))
=======
test-test-vector-15 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\207:\248\152Fz[zR\211=S\188\ETX~&B\168\218\153i\ETX\252%\"\ETB\233\192\&3\226\242\145")))) (UCon (tagCon bytestring (mkByteString "U\199\250CO^\216\205\236+z\234\193s")))) (UCon (tagCon bytestring (mkByteString "n\227\254\129\226<`\235#\DC2\178\NULk;%\230\131\142\STX\DLEf#\248D\196N\219\141\175\214j\176g\DLE\135\253\EM]\245\184\245\138\GSnR\175B\144\128S\213\\s!\SOH\NUL\146t\135\149\239\148\207\ACK"))))
>>>>>>> origin/master

expected-test-vector-15 : Result
expected-test-vector-15 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-15 : Set
pending-test-vector-15 = Pending (evalRaw test-test-vector-15 ≡ expected-test-vector-15)
```

## test-vector-16

```
-- builtin/semantics/verifyEd25519Signature/test-vector-16
test-test-vector-16 : Untyped
<<<<<<< HEAD
test-test-vector-16 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "fd2a565723163e29f53c9de3d5e8fbe36a7ab66e1439ec4eae9c0a604af291a5")))) (UCon (tagCon bytestring (mkByteString "0a688e79be24f866286d4646b5d81c")))) (UCon (tagCon bytestring (mkByteString "f68d04847e5b249737899c014d31c805c5007a62c0a10d50bb1538c5f35503951fbc1e08682f2cc0c92efe8f4985dec61dcbd54d4b94a22547d24451271c8b00"))))
=======
test-test-vector-16 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\253*VW#\SYN>)\245<\157\227\213\232\251\227jz\182n\DC49\236N\174\156\n`J\242\145\165")))) (UCon (tagCon bytestring (mkByteString "\nh\142y\190$\248f(mFF\181\216\FS")))) (UCon (tagCon bytestring (mkByteString "\246\141\EOT\132~[$\151\&7\137\156\SOHM1\200\ENQ\197\NULzb\192\161\rP\187\NAK8\197\243U\ETX\149\US\188\RS\bh/,\192\201.\254\143I\133\222\198\GS\203\213MK\148\162%G\210DQ'\FS\139\NUL"))))
>>>>>>> origin/master

expected-test-vector-16 : Result
expected-test-vector-16 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-16 : Set
pending-test-vector-16 = Pending (evalRaw test-test-vector-16 ≡ expected-test-vector-16)
```

## test-vector-17

```
-- builtin/semantics/verifyEd25519Signature/test-vector-17
test-test-vector-17 : Untyped
<<<<<<< HEAD
test-test-vector-17 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "34e5a8508c4743746962c066e4badea2201b8ab484de5c4f94476ccd2143955b")))) (UCon (tagCon bytestring (mkByteString "c942fa7ac6b23ab7ff612fdc8e68ef39")))) (UCon (tagCon bytestring (mkByteString "2a3d27dc40d0a8127949a3b7f908b3688f63b7f14f651aacd715940bdbe27a0809aac142f47ab0e1e44fa490ba87ce5392f33a891539caf1ef4c367cae54500c"))))
=======
test-test-vector-17 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "4\229\168P\140GCtib\192f\228\186\222\162 \ESC\138\180\132\222\\O\148Gl\205!C\149[")))) (UCon (tagCon bytestring (mkByteString "\201B\250z\198\178:\183\255a/\220\142h\239\&9")))) (UCon (tagCon bytestring (mkByteString "*='\220@\208\168\DC2yI\163\183\249\b\179h\143c\183\241Oe\SUB\172\215\NAK\148\v\219\226z\b\t\170\193B\244z\176\225\228O\164\144\186\135\206S\146\243:\137\NAK9\202\241\239L6|\174TP\f"))))
>>>>>>> origin/master

expected-test-vector-17 : Result
expected-test-vector-17 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-17 : Set
pending-test-vector-17 = Pending (evalRaw test-test-vector-17 ≡ expected-test-vector-17)
```

## test-vector-18

```
-- builtin/semantics/verifyEd25519Signature/test-vector-18
test-test-vector-18 : Untyped
<<<<<<< HEAD
test-test-vector-18 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "0445e456dacc7d5b0bbed23c8200cdb74bdcb03e4c7b73f0a2b9b46eac5d4372")))) (UCon (tagCon bytestring (mkByteString "7368724a5b0efb57d28d97622dbde725af")))) (UCon (tagCon bytestring (mkByteString "3653ccb21219202b8436fb41a32ba2618c4a133431e6e63463ceb3b6106c4d56e1d2ba165ba76eaad3dc39bffb130f1de3d8e6427db5b71938db4e272bc3e20b"))))
=======
test-test-vector-18 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\EOTE\228V\218\204}[\v\190\210<\130\NUL\205\183K\220\176>L{s\240\162\185\180n\172]Cr")))) (UCon (tagCon bytestring (mkByteString "shrJ[\SO\251W\210\141\151b-\189\231%\175")))) (UCon (tagCon bytestring (mkByteString "6S\204\178\DC2\EM +\132\&6\251A\163+\162a\140J\DC341\230\230\&4c\206\179\182\DLElMV\225\210\186\SYN[\167n\170\211\220\&9\191\251\DC3\SI\GS\227\216\230B}\181\183\EM8\219N'+\195\226\v"))))
>>>>>>> origin/master

expected-test-vector-18 : Result
expected-test-vector-18 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-18 : Set
pending-test-vector-18 = Pending (evalRaw test-test-vector-18 ≡ expected-test-vector-18)
```

## test-vector-19

```
-- builtin/semantics/verifyEd25519Signature/test-vector-19
test-test-vector-19 : Untyped
<<<<<<< HEAD
test-test-vector-19 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "74d29127f199d86a8676aec33b4ce3f225ccb191f52c191ccd1e8cca65213a6b")))) (UCon (tagCon bytestring (mkByteString "bd8e05033f3a8bcdcbf4beceb70901c82e31")))) (UCon (tagCon bytestring (mkByteString "fbe929d743a03c17910575492f3092ee2a2bf14a60a3fcacec74a58c7334510fc262db582791322d6c8c41f1700adb80027ecabc14270b703444ae3ee7623e0a"))))
=======
test-test-vector-19 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "t\210\145'\241\153\216j\134v\174\195;L\227\242%\204\177\145\245,\EM\FS\205\RS\140\202e!:k")))) (UCon (tagCon bytestring (mkByteString "\189\142\ENQ\ETX?:\139\205\203\244\190\206\183\t\SOH\200.1")))) (UCon (tagCon bytestring (mkByteString "\251\233)\215C\160<\ETB\145\ENQuI/0\146\238*+\241J`\163\252\172\236t\165\140s4Q\SI\194b\219X'\145\&2-l\140A\241p\n\219\128\STX~\202\188\DC4'\vp4D\174>\231b>\n"))))
>>>>>>> origin/master

expected-test-vector-19 : Result
expected-test-vector-19 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-19 : Set
pending-test-vector-19 = Pending (evalRaw test-test-vector-19 ≡ expected-test-vector-19)
```

## test-vector-20

```
-- builtin/semantics/verifyEd25519Signature/test-vector-20
test-test-vector-20 : Untyped
<<<<<<< HEAD
test-test-vector-20 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "5b96dca497875bf9664c5e75facf3f9bc54bae913d66ca15ee85f1491ca24d2c")))) (UCon (tagCon bytestring (mkByteString "8171456f8b907189b1d779e26bc5afbb08c67a")))) (UCon (tagCon bytestring (mkByteString "73bca64e9dd0db88138eedfafcea8f5436cfb74bfb0e7733cf349baa0c49775c56d5934e1d38e36f39b7c5beb0a836510c45126f8ec4b6810519905b0ca07c09"))))
=======
test-test-vector-20 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "[\150\220\164\151\135[\249fL^u\250\207?\155\197K\174\145=f\202\NAK\238\133\241I\FS\162M,")))) (UCon (tagCon bytestring (mkByteString "\129qEo\139\144q\137\177\215y\226k\197\175\187\b\198z")))) (UCon (tagCon bytestring (mkByteString "s\188\166N\157\208\219\136\DC3\142\237\250\252\234\143T6\207\183K\251\SOw3\207\&4\155\170\fIw\\V\213\147N\GS8\227o9\183\197\190\176\168\&6Q\fE\DC2o\142\196\182\129\ENQ\EM\144[\f\160|\t"))))
>>>>>>> origin/master

expected-test-vector-20 : Result
expected-test-vector-20 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-20 : Set
pending-test-vector-20 = Pending (evalRaw test-test-vector-20 ≡ expected-test-vector-20)
```

## test-vector-21

```
-- builtin/semantics/verifyEd25519Signature/test-vector-21
test-test-vector-21 : Untyped
<<<<<<< HEAD
test-test-vector-21 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "1ca281938529896535a7714e3584085b86ef9fec723f42819fc8dd5d8c00817f")))) (UCon (tagCon bytestring (mkByteString "8ba6a4c9a15a244a9c26bb2a59b1026f21348b49")))) (UCon (tagCon bytestring (mkByteString "a1adc2bc6a2d980662677e7fdff6424de7dba50f5795ca90fdf3e96e256f3285cac71d3360482e993d0294ba4ec7440c61affdf35fe83e6e04263937db93f105"))))
=======
test-test-vector-21 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\FS\162\129\147\133)\137e5\167qN5\132\b[\134\239\159\236r?B\129\159\200\221]\140\NUL\129\DEL")))) (UCon (tagCon bytestring (mkByteString "\139\166\164\201\161Z$J\156&\187*Y\177\STXo!4\139I")))) (UCon (tagCon bytestring (mkByteString "\161\173\194\188j-\152\ACKbg~\DEL\223\246BM\231\219\165\SIW\149\202\144\253\243\233n%o2\133\202\199\GS3`H.\153=\STX\148\186N\199D\fa\175\253\243_\232>n\EOT&97\219\147\241\ENQ"))))
>>>>>>> origin/master

expected-test-vector-21 : Result
expected-test-vector-21 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-21 : Set
pending-test-vector-21 = Pending (evalRaw test-test-vector-21 ≡ expected-test-vector-21)
```

## test-vector-22

```
-- builtin/semantics/verifyEd25519Signature/test-vector-22
test-test-vector-22 : Untyped
<<<<<<< HEAD
test-test-vector-22 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "7fae45dd0a05971026d410bc497af5be7d0827a82a145c203f625dfcb8b03ba8")))) (UCon (tagCon bytestring (mkByteString "1d566a6232bbaab3e6d8804bb518a498ed0f904986")))) (UCon (tagCon bytestring (mkByteString "bb61cf84de61862207c6a455258bc4db4e15eea0317ff88718b882a06b5cf6ec6fd20c5a269e5d5c805bafbcc579e2590af414c7c227273c102a10070cdfe80f"))))
=======
test-test-vector-22 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\DEL\174E\221\n\ENQ\151\DLE&\212\DLE\188Iz\245\190}\b'\168*\DC4\\ ?b]\252\184\176;\168")))) (UCon (tagCon bytestring (mkByteString "\GSVjb2\187\170\179\230\216\128K\181\CAN\164\152\237\SI\144I\134")))) (UCon (tagCon bytestring (mkByteString "\187a\207\132\222a\134\"\a\198\164U%\139\196\219N\NAK\238\160\&1\DEL\248\135\CAN\184\130\160k\\\246\236o\210\fZ&\158]\\\128[\175\188\197y\226Y\n\244\DC4\199\194''<\DLE*\DLE\a\f\223\232\SI"))))
>>>>>>> origin/master

expected-test-vector-22 : Result
expected-test-vector-22 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-22 : Set
pending-test-vector-22 = Pending (evalRaw test-test-vector-22 ≡ expected-test-vector-22)
```

## test-vector-23

```
-- builtin/semantics/verifyEd25519Signature/test-vector-23
test-test-vector-23 : Untyped
<<<<<<< HEAD
test-test-vector-23 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "48359b850d23f0715d94bb8bb75e7e14322eaf14f06f28a805403fbda002fc85")))) (UCon (tagCon bytestring (mkByteString "1b0afb0ac4ba9ab7b7172cddc9eb42bba1a64bce47d4")))) (UCon (tagCon bytestring (mkByteString "b6dcd09989dfbac54322a3ce87876e1d62134da998c79d24b50bd7a6a797d86a0e14dc9d7491d6c14a673c652cfbec9f962a38c945da3b2f0879d0b68a921300"))))
=======
test-test-vector-23 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "H5\155\133\r#\240q]\148\187\139\183^~\DC42.\175\DC4\240o(\168\ENQ@?\189\160\STX\252\133")))) (UCon (tagCon bytestring (mkByteString "\ESC\n\251\n\196\186\154\183\183\ETB,\221\201\235B\187\161\166K\206G\212")))) (UCon (tagCon bytestring (mkByteString "\182\220\208\153\137\223\186\197C\"\163\206\135\135n\GSb\DC3M\169\152\199\157$\181\v\215\166\167\151\216j\SO\DC4\220\157t\145\214\193Jg<e,\251\236\159\150*8\201E\218;/\by\208\182\138\146\DC3\NUL"))))
>>>>>>> origin/master

expected-test-vector-23 : Result
expected-test-vector-23 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-23 : Set
pending-test-vector-23 = Pending (evalRaw test-test-vector-23 ≡ expected-test-vector-23)
```

## test-vector-24

```
-- builtin/semantics/verifyEd25519Signature/test-vector-24
test-test-vector-24 : Untyped
<<<<<<< HEAD
test-test-vector-24 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "fdb30673402faf1c8033714f3517e47cc0f91fe70cf3836d6c23636e3fd2287c")))) (UCon (tagCon bytestring (mkByteString "507c94c8820d2a5793cbf3442b3d71936f35fe3afef316")))) (UCon (tagCon bytestring (mkByteString "7ef66e5e86f2360848e0014e94880ae2920ad8a3185a46b35d1e07dea8fa8ae4f6b843ba174d99fa7986654a0891c12a794455669375bf92af4cc2770b579e0c"))))
=======
test-test-vector-24 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\253\179\ACKs@/\175\FS\128\&3qO5\ETB\228|\192\249\US\231\f\243\131ml#cn?\210(|")))) (UCon (tagCon bytestring (mkByteString "P|\148\200\130\r*W\147\203\243D+=q\147o5\254:\254\243\SYN")))) (UCon (tagCon bytestring (mkByteString "~\246n^\134\242\&6\bH\224\SOHN\148\136\n\226\146\n\216\163\CANZF\179]\RS\a\222\168\250\138\228\246\184C\186\ETBM\153\250y\134eJ\b\145\193*yDUf\147u\191\146\175L\194w\vW\158\f"))))
>>>>>>> origin/master

expected-test-vector-24 : Result
expected-test-vector-24 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-24 : Set
pending-test-vector-24 = Pending (evalRaw test-test-vector-24 ≡ expected-test-vector-24)
```

## test-vector-25

```
-- builtin/semantics/verifyEd25519Signature/test-vector-25
test-test-vector-25 : Untyped
<<<<<<< HEAD
test-test-vector-25 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "b1d39801892027d58a8c64335163195893bfc1b61dbeca3260497e1f30371107")))) (UCon (tagCon bytestring (mkByteString "d3d615a8472d9962bb70c5b5466a3d983a4811046e2a0ef5")))) (UCon (tagCon bytestring (mkByteString "836afa764d9c48aa4770a4388b654e97b3c16f082967febca27f2fc47ddfd9244b03cfc729698acf5109704346b60b230f255430089ddc56912399d1122de70a"))))
=======
test-test-vector-25 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\177\211\152\SOH\137 '\213\138\140d3Qc\EMX\147\191\193\182\GS\190\202\&2`I~\US07\DC1\a")))) (UCon (tagCon bytestring (mkByteString "\211\214\NAK\168G-\153b\187p\197\181Fj=\152:H\DC1\EOTn*\SO\245")))) (UCon (tagCon bytestring (mkByteString "\131j\250vM\156H\170Gp\164\&8\139eN\151\179\193o\b)g\254\188\162\DEL/\196}\223\217$K\ETX\207\199)i\138\207Q\tpCF\182\v#\SI%T0\b\157\220V\145#\153\209\DC2-\231\n"))))
>>>>>>> origin/master

expected-test-vector-25 : Result
expected-test-vector-25 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-25 : Set
pending-test-vector-25 = Pending (evalRaw test-test-vector-25 ≡ expected-test-vector-25)
```

## test-vector-26

```
-- builtin/semantics/verifyEd25519Signature/test-vector-26
test-test-vector-26 : Untyped
<<<<<<< HEAD
test-test-vector-26 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "d0c846f97fe28585c0ee159015d64c56311c886eddcc185d296dbb165d2625d6")))) (UCon (tagCon bytestring (mkByteString "6ada80b6fa84f7034920789e8536b82d5e4678059aed27f71c")))) (UCon (tagCon bytestring (mkByteString "16e462a29a6dd498685a3718b3eed00cc1598601ee47820486032d6b9acc9bf89f57684e08d8c0f05589cda2882a05dc4c63f9d0431d6552710812433003bc08"))))
=======
test-test-vector-26 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\208\200F\249\DEL\226\133\133\192\238\NAK\144\NAK\214LV1\FS\136n\221\204\CAN])m\187\SYN]&%\214")))) (UCon (tagCon bytestring (mkByteString "j\218\128\182\250\132\247\ETXI x\158\133\&6\184-^Fx\ENQ\154\237'\247\FS")))) (UCon (tagCon bytestring (mkByteString "\SYN\228b\162\154m\212\152hZ7\CAN\179\238\208\f\193Y\134\SOH\238G\130\EOT\134\ETX-k\154\204\155\248\159WhN\b\216\192\240U\137\205\162\136*\ENQ\220Lc\249\208C\GSeRq\b\DC2C0\ETX\188\b"))))
>>>>>>> origin/master

expected-test-vector-26 : Result
expected-test-vector-26 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-26 : Set
pending-test-vector-26 = Pending (evalRaw test-test-vector-26 ≡ expected-test-vector-26)
```

## test-vector-27

```
-- builtin/semantics/verifyEd25519Signature/test-vector-27
test-test-vector-27 : Untyped
<<<<<<< HEAD
test-test-vector-27 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "2bf32ba142ba4622d8f3e29ecd85eea07b9c47be9d64412c9b510b27dd218b23")))) (UCon (tagCon bytestring (mkByteString "82cb53c4d5a013bae5070759ec06c3c6955ab7a4050958ec328c")))) (UCon (tagCon bytestring (mkByteString "881f5b8c5a030df0f75b6634b070dd27bd1ee3c08738ae349338b3ee6469bbf9760b13578a237d5182535ede121283027a90b5f865d63a6537dca07b44049a0f"))))
=======
test-test-vector-27 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "+\243+\161B\186F\"\216\243\226\158\205\133\238\160{\156G\190\157dA,\155Q\v'\221!\139#")))) (UCon (tagCon bytestring (mkByteString "\130\203S\196\213\160\DC3\186\229\a\aY\236\ACK\195\198\149Z\183\164\ENQ\tX\236\&2\140")))) (UCon (tagCon bytestring (mkByteString "\136\US[\140Z\ETX\r\240\247[f4\176p\221'\189\RS\227\192\135\&8\174\&4\147\&8\179\238di\187\249v\v\DC3W\138#}Q\130S^\222\DC2\DC2\131\STXz\144\181\248e\214:e7\220\160{D\EOT\154\SI"))))
>>>>>>> origin/master

expected-test-vector-27 : Result
expected-test-vector-27 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-27 : Set
pending-test-vector-27 = Pending (evalRaw test-test-vector-27 ≡ expected-test-vector-27)
```

## test-vector-28

```
-- builtin/semantics/verifyEd25519Signature/test-vector-28
test-test-vector-28 : Untyped
<<<<<<< HEAD
test-test-vector-28 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "94d23d977c33e49e5e4992c68f25ec99a27c41ce6b91f2bfa0cd8292fe962835")))) (UCon (tagCon bytestring (mkByteString "a9a8cbb0ad585124e522abbfb40533bdd6f49347b55b18e8558cb0")))) (UCon (tagCon bytestring (mkByteString "3acd39bec8c3cd2b44299722b5850a0400c1443590fd4861d59aae7496acb3df73fc3fdf7969ae5f50ba47dddc435246e5fd376f6b891cd4c2caf5d614b6170c"))))
=======
test-test-vector-28 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\148\210=\151|3\228\158^I\146\198\143%\236\153\162|A\206k\145\242\191\160\205\130\146\254\150(5")))) (UCon (tagCon bytestring (mkByteString "\169\168\203\176\173XQ$\229\"\171\191\180\ENQ3\189\214\244\147G\181[\CAN\232U\140\176")))) (UCon (tagCon bytestring (mkByteString ":\205\&9\190\200\195\205+D)\151\"\181\133\n\EOT\NUL\193D5\144\253Ha\213\154\174t\150\172\179\223s\252?\223yi\174_P\186G\221\220CRF\229\253\&7ok\137\FS\212\194\202\245\214\DC4\182\ETB\f"))))
>>>>>>> origin/master

expected-test-vector-28 : Result
expected-test-vector-28 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-28 : Set
pending-test-vector-28 = Pending (evalRaw test-test-vector-28 ≡ expected-test-vector-28)
```

## test-vector-29

```
-- builtin/semantics/verifyEd25519Signature/test-vector-29
test-test-vector-29 : Untyped
<<<<<<< HEAD
test-test-vector-29 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "9d084aa8b97a6b9bafa496dbc6f76f3306a116c9d917e681520a0f914369427e")))) (UCon (tagCon bytestring (mkByteString "5cb6f9aa59b80eca14f6a68fb40cf07b794e75171fba96262c1c6adc")))) (UCon (tagCon bytestring (mkByteString "f5875423781b66216cb5e8998de5d9ffc29d1d67107054ace3374503a9c3ef811577f269de81296744bd706f1ac478caf09b54cdf871b3f802bd57f9a6cb9101"))))
=======
test-test-vector-29 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\157\bJ\168\185zk\155\175\164\150\219\198\247o3\ACK\161\SYN\201\217\ETB\230\129R\n\SI\145CiB~")))) (UCon (tagCon bytestring (mkByteString "\\\182\249\170Y\184\SO\202\DC4\246\166\143\180\f\240{yNu\ETB\US\186\150&,\FSj\220")))) (UCon (tagCon bytestring (mkByteString "\245\135T#x\ESCf!l\181\232\153\141\229\217\255\194\157\GSg\DLEpT\172\227\&7E\ETX\169\195\239\129\NAKw\242i\222\129)gD\189po\SUB\196x\202\240\155T\205\248q\179\248\STX\189W\249\166\203\145\SOH"))))
>>>>>>> origin/master

expected-test-vector-29 : Result
expected-test-vector-29 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-29 : Set
pending-test-vector-29 = Pending (evalRaw test-test-vector-29 ≡ expected-test-vector-29)
```

## test-vector-30

```
-- builtin/semantics/verifyEd25519Signature/test-vector-30
test-test-vector-30 : Untyped
<<<<<<< HEAD
test-test-vector-30 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "16cee8a3f2631834c88b670897ff0b08ce90cc147b4593b3f1f403727f7e7ad5")))) (UCon (tagCon bytestring (mkByteString "32fe27994124202153b5c70d3813fdee9c2aa6e7dc743d4d535f1840a5")))) (UCon (tagCon bytestring (mkByteString "d834197c1a3080614e0a5fa0aaaa808824f21c38d692e6ffbd200f7dfb3c8f44402a7382180b98ad0afc8eec1a02acecf3cb7fde627b9f18111f260ab1db9a07"))))
=======
test-test-vector-30 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "\SYN\206\232\163\242c\CAN4\200\139g\b\151\255\v\b\206\144\204\DC4{E\147\179\241\244\ETXr\DEL~z\213")))) (UCon (tagCon bytestring (mkByteString "2\254'\153A$ !S\181\199\r8\DC3\253\238\156*\166\231\220t=MS_\CAN@\165")))) (UCon (tagCon bytestring (mkByteString "\216\&4\EM|\SUB0\128aN\n_\160\170\170\128\136$\242\FS8\214\146\230\255\189 \SI}\251<\143D@*s\130\CAN\v\152\173\n\252\142\236\SUB\STX\172\236\243\203\DEL\222b{\159\CAN\DC1\US&\n\177\219\154\a"))))
>>>>>>> origin/master

expected-test-vector-30 : Result
expected-test-vector-30 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-30 : Set
pending-test-vector-30 = Pending (evalRaw test-test-vector-30 ≡ expected-test-vector-30)
```

## test-vector-31

```
-- builtin/semantics/verifyEd25519Signature/test-vector-31
test-test-vector-31 : Untyped
<<<<<<< HEAD
test-test-vector-31 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "23be323c562dfd71ce65f5bba56a74a3a6dfc36b573d2f94f635c7f9b4fd5a5b")))) (UCon (tagCon bytestring (mkByteString "bb3172795710fe00054d3b5dfef8a11623582da68bf8e46d72d27cece2aa")))) (UCon (tagCon bytestring (mkByteString "0f8fad1e6bde771b4f5420eac75c378bae6db5ac6650cd2bc210c1823b432b48e016b10595458ffab92f7a8989b293ceb8dfed6c243a2038fc06652aaaf16f02"))))
=======
test-test-vector-31 = (UApp (UApp (UApp (UBuiltin verifyEd25519Signature) (UCon (tagCon bytestring (mkByteString "#\190\&2<V-\253q\206e\245\187\165jt\163\166\223\195kW=/\148\246\&5\199\249\180\253Z[")))) (UCon (tagCon bytestring (mkByteString "\187\&1ryW\DLE\254\NUL\ENQM;]\254\248\161\SYN#X-\166\139\248\228mr\210|\236\226\170")))) (UCon (tagCon bytestring (mkByteString "\SI\143\173\RSk\222w\ESCOT \234\199\\7\139\174m\181\172fP\205+\194\DLE\193\130;C+H\224\SYN\177\ENQ\149E\143\250\185/z\137\137\178\147\206\184\223\237l$: 8\252\ACKe*\170\241o\STX"))))
>>>>>>> origin/master

expected-test-vector-31 : Result
expected-test-vector-31 = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `verifyEd25519Signature`.
=======
-- Pending: bytestring constant; postulated builtin `verifyEd25519Signature`.
>>>>>>> origin/master
pending-test-vector-31 : Set
pending-test-vector-31 = Pending (evalRaw test-test-vector-31 ≡ expected-test-vector-31)
```
