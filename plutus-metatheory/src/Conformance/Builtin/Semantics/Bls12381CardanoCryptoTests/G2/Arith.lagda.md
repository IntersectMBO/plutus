---
title: Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G2.Arith
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
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381-cardano-crypto-tests/G2/arith`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G2.Arith where

open import Conformance.Eval
```

## add

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/arith/add
-- Check that adding two random points in G2 gives the expected result.
test-add : Untyped
<<<<<<< HEAD
test-add = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b5ed6482bf5486831a9eb445b8b9a77aa6330005b8b432523c69fee7085d3032856de9f857c55ac9745eabcf14894205149cc67393687289e6c2728be69ad1f8ea1a6c0a5a65bf93eca984f3dac5da1abc6f7156ccbc5a33c655f7b17724eb19"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a6cc0f01663fd65a95d1359758ebe3a412ce05f4242b0c1f5964351b38e188362a8ceb6c2f86d3f7e5f73b60cd04288005d2a50f8ddf1751d7a915515054276fbae7569c3f18c614c9954177d8e745e98404654cf759d4747b0c806bbd336b7d"))))))) (UCon (tagCon bytestring (mkByteString "b3db03681aaf0d218be32f7cc94bd6a975c6870b4a1d4e461b77b60eee2461ca367154b0c4583b2d5f81124aa21fdf3e09ff6b54ce7c57572283a175fba381a32ac6f46abaf11cdbaeb206dcd7d4269caa4d0ebbb3adc1b8fce42ccfa855ea83"))))
=======
test-add = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\181\237d\130\191T\134\131\SUB\158\180E\184\185\167z\166\&3\NUL\ENQ\184\180\&2R<i\254\231\b]02\133m\233\248W\197Z\201t^\171\207\DC4\137B\ENQ\DC4\156\198s\147hr\137\230\194r\139\230\154\209\248\234\SUBl\nZe\191\147\236\169\132\243\218\197\218\SUB\188oqV\204\188Z3\198U\247\177w$\235\EM"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\166\204\SI\SOHf?\214Z\149\209\&5\151X\235\227\164\DC2\206\ENQ\244$+\f\USYd5\ESC8\225\136\&6*\140\235l/\134\211\247\229\247;`\205\EOT(\128\ENQ\210\165\SI\141\223\ETBQ\215\169\NAKQPT'o\186\231V\156?\CAN\198\DC4\201\149Aw\216\231E\233\132\EOTeL\247Y\212t{\f\128k\189\&3k}"))))))) (UCon (tagCon bytestring (mkByteString "\179\219\ETXh\SUB\175\r!\139\227/|\201K\214\169u\198\135\vJ\GSNF\ESCw\182\SO\238$a\202\&6qT\176\196X;-_\129\DC2J\162\US\223>\t\255kT\206|WW\"\131\161u\251\163\129\163*\198\244j\186\241\FS\219\174\178\ACK\220\215\212&\156\170M\SO\187\179\173\193\184\252\228,\207\168U\234\131"))))
>>>>>>> origin/master

expected-add : Result
expected-add = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
>>>>>>> origin/master
pending-add : Set
pending-add = Pending (evalRaw test-add ≡ expected-add)
```

## neg

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/arith/neg
-- Check that negating a random point in G2 gives the expected result.
test-neg : Untyped
<<<<<<< HEAD
test-neg = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-neg) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b5ed6482bf5486831a9eb445b8b9a77aa6330005b8b432523c69fee7085d3032856de9f857c55ac9745eabcf14894205149cc67393687289e6c2728be69ad1f8ea1a6c0a5a65bf93eca984f3dac5da1abc6f7156ccbc5a33c655f7b17724eb19"))))))) (UCon (tagCon bytestring (mkByteString "95ed6482bf5486831a9eb445b8b9a77aa6330005b8b432523c69fee7085d3032856de9f857c55ac9745eabcf14894205149cc67393687289e6c2728be69ad1f8ea1a6c0a5a65bf93eca984f3dac5da1abc6f7156ccbc5a33c655f7b17724eb19"))))
=======
test-neg = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-neg) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\181\237d\130\191T\134\131\SUB\158\180E\184\185\167z\166\&3\NUL\ENQ\184\180\&2R<i\254\231\b]02\133m\233\248W\197Z\201t^\171\207\DC4\137B\ENQ\DC4\156\198s\147hr\137\230\194r\139\230\154\209\248\234\SUBl\nZe\191\147\236\169\132\243\218\197\218\SUB\188oqV\204\188Z3\198U\247\177w$\235\EM"))))))) (UCon (tagCon bytestring (mkByteString "\149\237d\130\191T\134\131\SUB\158\180E\184\185\167z\166\&3\NUL\ENQ\184\180\&2R<i\254\231\b]02\133m\233\248W\197Z\201t^\171\207\DC4\137B\ENQ\DC4\156\198s\147hr\137\230\194r\139\230\154\209\248\234\SUBl\nZe\191\147\236\169\132\243\218\197\218\SUB\188oqV\204\188Z3\198U\247\177w$\235\EM"))))
>>>>>>> origin/master

expected-neg : Result
expected-neg = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-neg`; postulated builtin `bls12-381-G2-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-neg`; postulated builtin `bls12-381-G2-uncompress`.
>>>>>>> origin/master
pending-neg : Set
pending-neg = Pending (evalRaw test-neg ≡ expected-neg)
```

## scalarMul

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/arith/scalarMul
-- Scalar multiplication gives the correct result.
test-scalarMul : Untyped
<<<<<<< HEAD
test-scalarMul = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 29342537169447282925541144552701591957563885683358707334406144036950193508773)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a6cc0f01663fd65a95d1359758ebe3a412ce05f4242b0c1f5964351b38e188362a8ceb6c2f86d3f7e5f73b60cd04288005d2a50f8ddf1751d7a915515054276fbae7569c3f18c614c9954177d8e745e98404654cf759d4747b0c806bbd336b7d"))))))) (UCon (tagCon bytestring (mkByteString "89b8e839c317ab3c735c6a65122fff4654f469c30c480701f6e4d9f311f3c5f3411c7cd2876c539bf56f983d14e550b5172765f62bba1235394a33413c21667a57214e9a6f2516f8d7bf57321c20bf8cd8ecd290691ad6bd5ab9e391304240a4"))))
=======
test-scalarMul = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 29342537169447282925541144552701591957563885683358707334406144036950193508773)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\166\204\SI\SOHf?\214Z\149\209\&5\151X\235\227\164\DC2\206\ENQ\244$+\f\USYd5\ESC8\225\136\&6*\140\235l/\134\211\247\229\247;`\205\EOT(\128\ENQ\210\165\SI\141\223\ETBQ\215\169\NAKQPT'o\186\231V\156?\CAN\198\DC4\201\149Aw\216\231E\233\132\EOTeL\247Y\212t{\f\128k\189\&3k}"))))))) (UCon (tagCon bytestring (mkByteString "\137\184\232\&9\195\ETB\171<s\\je\DC2/\255FT\244i\195\fH\a\SOH\246\228\217\243\DC1\243\197\243A\FS|\210\135lS\155\245o\152=\DC4\229P\181\ETB'e\246+\186\DC259J3A<!fzW!N\154o%\SYN\248\215\191W2\FS \191\140\216\236\210\144i\SUB\214\189Z\185\227\145\&0B@\164"))))
>>>>>>> origin/master

expected-scalarMul : Result
expected-scalarMul = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
>>>>>>> origin/master
pending-scalarMul : Set
pending-scalarMul = Pending (evalRaw test-scalarMul ≡ expected-scalarMul)
```
