---
title: Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.Pairing
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381-cardano-crypto-tests/pairing`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.Pairing where

open import Conformance.Eval
```

## balanced

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/balanced
-- <[a]P,Q> = <P,[a]Q>
test-balanced : Untyped
test-balanced = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\139\170O?\205\137P3\249\&4\148\176@\204\215\223\183|\183Y\205.\NAK\v\255\244&Hs\ETBE\t\205\"#\EOT#\183\b\150\177|\143\195f\SIk!"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\182p)\251\243\171\142b\171kI\159T\NAK7\252\a\217Fnf\131\146\223+\193\151b\215\220H\182K\224\154D\140\212m\191\226\CAN\EM\169\FS\208\171\&2\ENQ\241\&1j\209\204\&2\133??\SUB\GS\ACKI\DEL\\\251\194\215S\223\192\ESC\255\ETBz\222\185?$\212R\EOTT5\220n\178\159V\DLE\182l\208\221?\179R")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\132\EOTc\170/,\218\137\152[\US?^\180;\156)\128\151e\210t}`sK\EM\214\249\ACK\DLE\239\253\252P\n\247\212X\163\231\140\238\tE\221\198i"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\168\SI1\GS\182\242\253\196T\EOT\135\SILU\182Z\154Y\163^\252\250*|Y_9U\"`v\187\170\&3\228\ETX\192\212t\148\149\217B;\128o\157\190\b\204\167p\224\143\165\&5\218\239\182\219\162\237\182/\139\154\255k\174\131\191H\129\155\205\249\143\a\231\157\232c^\133!\221\236\174\EM\176\SUBgw\188F\132"))))))

expected-balanced : Result
expected-balanced = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-balanced : Set
pending-balanced = Pending (evalRaw test-balanced ≡ expected-balanced)
```

## left-additive

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/left-additive
-- <[a]P,Q><[b]P,Q> = <[a+b]P,Q>
test-left-additive : Untyped
test-left-additive = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-mulMlResult) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\139\170O?\205\137P3\249\&4\148\176@\204\215\223\183|\183Y\205.\NAK\v\255\244&Hs\ETBE\t\205\"#\EOT#\183\b\150\177|\143\195f\SIk!"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\182p)\251\243\171\142b\171kI\159T\NAK7\252\a\217Fnf\131\146\223+\193\151b\215\220H\182K\224\154D\140\212m\191\226\CAN\EM\169\FS\208\171\&2\ENQ\241\&1j\209\204\&2\133??\SUB\GS\ACKI\DEL\\\251\194\215S\223\192\ESC\255\ETBz\222\185?$\212R\EOTT5\220n\178\159V\DLE\182l\208\221?\179R")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\164\169%\203\156\ENQ\128\193L\188\142\197DG\235 \a\ETX6\166\FS4\156jd\176\216~M\184\157ws@!\205\136\226\218\&6\155\221\133\192Q\140f\196"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\182p)\251\243\171\142b\171kI\159T\NAK7\252\a\217Fnf\131\146\223+\193\151b\215\220H\182K\224\154D\140\212m\191\226\CAN\EM\169\FS\208\171\&2\ENQ\241\&1j\209\204\&2\133??\SUB\GS\ACKI\DEL\\\251\194\215S\223\192\ESC\255\ETBz\222\185?$\212R\EOTT5\220n\178\159V\DLE\182l\208\221?\179R"))))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\174\207T\b1\135\STXjkh\158p\175T7Z\183\204m\r1\SUB\203b\ETXs\n)\EOTeMn\146\248.b\NULl\r^!\tAU\235\147\204\152"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\182p)\251\243\171\142b\171kI\159T\NAK7\252\a\217Fnf\131\146\223+\193\151b\215\220H\182K\224\154D\140\212m\191\226\CAN\EM\169\FS\208\171\&2\ENQ\241\&1j\209\204\&2\133??\SUB\GS\ACKI\DEL\\\251\194\215S\223\192\ESC\255\ETBz\222\185?$\212R\EOTT5\220n\178\159V\DLE\182l\208\221?\179R"))))))

expected-left-additive : Result
expected-left-additive = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-mulMlResult`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-left-additive : Set
pending-left-additive = Pending (evalRaw test-left-additive ≡ expected-left-additive)
```

## left-multiplicative

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/left-multiplicative
-- <[a]P,[b]Q> = <[ab]P,Q>
test-left-multiplicative : Untyped
test-left-multiplicative = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\139\170O?\205\137P3\249\&4\148\176@\204\215\223\183|\183Y\205.\NAK\v\255\244&Hs\ETBE\t\205\"#\EOT#\183\b\150\177|\143\195f\SIk!"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\153\ACK\161_\249Y\180\150\244x\221\ETB4\139\&2\192\&3#m\181\167Cwh\163\f\\\232}\155j\223\167\191\"#\160r\FS\147\169/3\171\172\155/\175\NUL\210^H\176\243\204RYRd\239\154\208\170{\129\226\v<\134\&4\213w\136?\245\252#s\160!\161\229x&\244 \167O<\224\251\210\220\247\148\NAK")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\178\187$3D\FSE+x\245\190\145\SUB\161\&6\221,\136j\154\195)\203l\128^P\213%X\145\252\195\137\177\EM\EOT2\241j\DLE\156oC\US\SI\128#"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\182p)\251\243\171\142b\171kI\159T\NAK7\252\a\217Fnf\131\146\223+\193\151b\215\220H\182K\224\154D\140\212m\191\226\CAN\EM\169\FS\208\171\&2\ENQ\241\&1j\209\204\&2\133??\SUB\GS\ACKI\DEL\\\251\194\215S\223\192\ESC\255\ETBz\222\185?$\212R\EOTT5\220n\178\159V\DLE\182l\208\221?\179R"))))))

expected-left-multiplicative : Result
expected-left-multiplicative = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-left-multiplicative : Set
pending-left-multiplicative = Pending (evalRaw test-left-multiplicative ≡ expected-left-multiplicative)
```

## right-additive

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/right-additive
-- <P,[a]Q><P,[b]Q> = <P,[a+b]Q>
test-right-additive : Untyped
test-right-additive = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-mulMlResult) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\132\EOTc\170/,\218\137\152[\US?^\180;\156)\128\151e\210t}`sK\EM\214\249\ACK\DLE\239\253\252P\n\247\212X\163\231\140\238\tE\221\198i"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\168\SI1\GS\182\242\253\196T\EOT\135\SILU\182Z\154Y\163^\252\250*|Y_9U\"`v\187\170\&3\228\ETX\192\212t\148\149\217B;\128o\157\190\b\204\167p\224\143\165\&5\218\239\182\219\162\237\182/\139\154\255k\174\131\191H\129\155\205\249\143\a\231\157\232c^\133!\221\236\174\EM\176\SUBgw\188F\132")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\132\EOTc\170/,\218\137\152[\US?^\180;\156)\128\151e\210t}`sK\EM\214\249\ACK\DLE\239\253\252P\n\247\212X\163\231\140\238\tE\221\198i"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\153\ACK\161_\249Y\180\150\244x\221\ETB4\139\&2\192\&3#m\181\167Cwh\163\f\\\232}\155j\223\167\191\"#\160r\FS\147\169/3\171\172\155/\175\NUL\210^H\176\243\204RYRd\239\154\208\170{\129\226\v<\134\&4\213w\136?\245\252#s\160!\161\229x&\244 \167O<\224\251\210\220\247\148\NAK"))))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\132\EOTc\170/,\218\137\152[\US?^\180;\156)\128\151e\210t}`sK\EM\214\249\ACK\DLE\239\253\252P\n\247\212X\163\231\140\238\tE\221\198i"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\166;\228\161\167v\202\220\DEL\194\226\216#\188\201\ENQ\248\249\203\SO\190f#`\210\141\153d\176\"\169\156\227JH\178\233<\252\238\188\155\193\215\154\&38\218\ETX\164\DC3\147qr9\230mM\176j\135Q\v\153\254\EOT\176\132\f\135\196\ENQ\DLE0\178^V\186\&4$\141\158\211\f\130\232\229\SOH\166\SYN\tr\153\238\253b"))))))

expected-right-additive : Result
expected-right-additive = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-mulMlResult`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-right-additive : Set
pending-right-additive = Pending (evalRaw test-right-additive ≡ expected-right-additive)
```

## right-multiplicative

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/right-multiplicative
-- <[a]P,[b]Q> = <P,[ab]Q>
test-right-multiplicative : Untyped
test-right-multiplicative = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\139\170O?\205\137P3\249\&4\148\176@\204\215\223\183|\183Y\205.\NAK\v\255\244&Hs\ETBE\t\205\"#\EOT#\183\b\150\177|\143\195f\SIk!"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\153\ACK\161_\249Y\180\150\244x\221\ETB4\139\&2\192\&3#m\181\167Cwh\163\f\\\232}\155j\223\167\191\"#\160r\FS\147\169/3\171\172\155/\175\NUL\210^H\176\243\204RYRd\239\154\208\170{\129\226\v<\134\&4\213w\136?\245\252#s\160!\161\229x&\244 \167O<\224\251\210\220\247\148\NAK")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\132\EOTc\170/,\218\137\152[\US?^\180;\156)\128\151e\210t}`sK\EM\214\249\ACK\DLE\239\253\252P\n\247\212X\163\231\140\238\tE\221\198i"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\130`oLw\FS\166\133\191\193\187\156Q\200\134\208\218\160\246?\187\SIj$\181\DC2\161\185\185-@\RSUl\191\253\194\EOT\192\168Q\146\200e\237s\248\t\r\165\142\205\SYN\144\213\163\178\&6\204]@\169\137\136\249`*m\DC1N\219Y\149N\244\226\SYN\146\242\212\130\EM\174\172\185d`HI3`Y\206\236\230\159"))))))

expected-right-multiplicative : Result
expected-right-multiplicative = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-right-multiplicative : Set
pending-right-multiplicative = Pending (evalRaw test-right-multiplicative ≡ expected-right-multiplicative)
```

## swap-scalars

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/pairing/swap-scalars
-- <[a]P,[b]Q> = <[b]P,[a]Q>
test-swap-scalars : Untyped
test-swap-scalars = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\139\170O?\205\137P3\249\&4\148\176@\204\215\223\183|\183Y\205.\NAK\v\255\244&Hs\ETBE\t\205\"#\EOT#\183\b\150\177|\143\195f\SIk!"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\153\ACK\161_\249Y\180\150\244x\221\ETB4\139\&2\192\&3#m\181\167Cwh\163\f\\\232}\155j\223\167\191\"#\160r\FS\147\169/3\171\172\155/\175\NUL\210^H\176\243\204RYRd\239\154\208\170{\129\226\v<\134\&4\213w\136?\245\252#s\160!\161\229x&\244 \167O<\224\251\210\220\247\148\NAK")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\164\169%\203\156\ENQ\128\193L\188\142\197DG\235 \a\ETX6\166\FS4\156jd\176\216~M\184\157ws@!\205\136\226\218\&6\155\221\133\192Q\140f\196"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\168\SI1\GS\182\242\253\196T\EOT\135\SILU\182Z\154Y\163^\252\250*|Y_9U\"`v\187\170\&3\228\ETX\192\212t\148\149\217B;\128o\157\190\b\204\167p\224\143\165\&5\218\239\182\219\162\237\182/\139\154\255k\174\131\191H\129\155\205\249\143\a\231\157\232c^\133!\221\236\174\EM\176\SUBgw\188F\132"))))))

expected-swap-scalars : Result
expected-swap-scalars = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-swap-scalars : Set
pending-swap-scalars = Pending (evalRaw test-swap-scalars ≡ expected-swap-scalars)
```
