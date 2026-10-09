---
title: Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G2.Arith
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
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
test-add = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\181\237d\130\191T\134\131\SUB\158\180E\184\185\167z\166\&3\NUL\ENQ\184\180\&2R<i\254\231\b]02\133m\233\248W\197Z\201t^\171\207\DC4\137B\ENQ\DC4\156\198s\147hr\137\230\194r\139\230\154\209\248\234\SUBl\nZe\191\147\236\169\132\243\218\197\218\SUB\188oqV\204\188Z3\198U\247\177w$\235\EM"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\166\204\SI\SOHf?\214Z\149\209\&5\151X\235\227\164\DC2\206\ENQ\244$+\f\USYd5\ESC8\225\136\&6*\140\235l/\134\211\247\229\247;`\205\EOT(\128\ENQ\210\165\SI\141\223\ETBQ\215\169\NAKQPT'o\186\231V\156?\CAN\198\DC4\201\149Aw\216\231E\233\132\EOTeL\247Y\212t{\f\128k\189\&3k}"))))))) (UCon (tagCon bytestring (mkByteString "\179\219\ETXh\SUB\175\r!\139\227/|\201K\214\169u\198\135\vJ\GSNF\ESCw\182\SO\238$a\202\&6qT\176\196X;-_\129\DC2J\162\US\223>\t\255kT\206|WW\"\131\161u\251\163\129\163*\198\244j\186\241\FS\219\174\178\ACK\220\215\212&\156\170M\SO\187\179\173\193\184\252\228,\207\168U\234\131"))))

expected-add : Result
expected-add = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
pending-add : Set
pending-add = Pending (evalRaw test-add ≡ expected-add)
```

## neg

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/arith/neg
-- Check that negating a random point in G2 gives the expected result.
test-neg : Untyped
test-neg = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-neg) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\181\237d\130\191T\134\131\SUB\158\180E\184\185\167z\166\&3\NUL\ENQ\184\180\&2R<i\254\231\b]02\133m\233\248W\197Z\201t^\171\207\DC4\137B\ENQ\DC4\156\198s\147hr\137\230\194r\139\230\154\209\248\234\SUBl\nZe\191\147\236\169\132\243\218\197\218\SUB\188oqV\204\188Z3\198U\247\177w$\235\EM"))))))) (UCon (tagCon bytestring (mkByteString "\149\237d\130\191T\134\131\SUB\158\180E\184\185\167z\166\&3\NUL\ENQ\184\180\&2R<i\254\231\b]02\133m\233\248W\197Z\201t^\171\207\DC4\137B\ENQ\DC4\156\198s\147hr\137\230\194r\139\230\154\209\248\234\SUBl\nZe\191\147\236\169\132\243\218\197\218\SUB\188oqV\204\188Z3\198U\247\177w$\235\EM"))))

expected-neg : Result
expected-neg = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-neg`; postulated builtin `bls12-381-G2-uncompress`.
pending-neg : Set
pending-neg = Pending (evalRaw test-neg ≡ expected-neg)
```

## scalarMul

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/arith/scalarMul
-- Scalar multiplication gives the correct result.
test-scalarMul : Untyped
test-scalarMul = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 29342537169447282925541144552701591957563885683358707334406144036950193508773)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\166\204\SI\SOHf?\214Z\149\209\&5\151X\235\227\164\DC2\206\ENQ\244$+\f\USYd5\ESC8\225\136\&6*\140\235l/\134\211\247\229\247;`\205\EOT(\128\ENQ\210\165\SI\141\223\ETBQ\215\169\NAKQPT'o\186\231V\156?\CAN\198\DC4\201\149Aw\216\231E\233\132\EOTeL\247Y\212t{\f\128k\189\&3k}"))))))) (UCon (tagCon bytestring (mkByteString "\137\184\232\&9\195\ETB\171<s\\je\DC2/\255FT\244i\195\fH\a\SOH\246\228\217\243\DC1\243\197\243A\FS|\210\135lS\155\245o\152=\DC4\229P\181\ETB'e\246+\186\DC259J3A<!fzW!N\154o%\SYN\248\215\191W2\FS \191\140\216\236\210\144i\SUB\214\189Z\185\227\145\&0B@\164"))))

expected-scalarMul : Result
expected-scalarMul = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-scalarMul : Set
pending-scalarMul = Pending (evalRaw test-scalarMul ≡ expected-scalarMul)
```
