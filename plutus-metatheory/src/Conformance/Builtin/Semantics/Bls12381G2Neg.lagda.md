---
title: Conformance.Builtin.Semantics.Bls12381G2Neg
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G2_neg`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G2Neg where

open import Conformance.Eval
```

## add-neg

```
-- builtin/semantics/bls12_381_G2_neg/add-neg
-- Check that adding a random point to its negative gives the zero element.
test-add-neg : Untyped
test-add-neg = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))) (UApp (UBuiltin bls12-381-G2-neg) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241")))))))

expected-add-neg : Result
expected-add-neg = success (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`; postulated builtin `bls12-381-G2-neg`.
pending-add-neg : Set
pending-add-neg = Pending (evalRaw test-add-neg ≡ expected-add-neg)
```

## neg

```
-- builtin/semantics/bls12_381_G2_neg/neg
-- Check that hashing a random bytestring gives the expected result.
test-neg : Untyped
test-neg = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-neg) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*"))))))

expected-neg : Result
expected-neg = success (UCon (tagCon bytestring (mkByteString "\163\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-neg`; postulated builtin `bls12-381-G2-uncompress`.
pending-neg : Set
pending-neg = Pending (evalRaw test-neg ≡ expected-neg)
```

## neg-zero

```
-- builtin/semantics/bls12_381_G2_neg/neg-zero
-- The negative of the zero point is the zero point.
test-neg-zero : Untyped
test-neg-zero = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-neg) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))))

expected-neg-zero : Result
expected-neg-zero = success (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-neg`; postulated builtin `bls12-381-G2-uncompress`.
pending-neg-zero : Set
pending-neg-zero = Pending (evalRaw test-neg-zero ≡ expected-neg-zero)
```
