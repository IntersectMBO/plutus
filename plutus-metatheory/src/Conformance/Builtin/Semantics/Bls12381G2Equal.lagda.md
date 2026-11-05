---
title: Conformance.Builtin.Semantics.Bls12381G2Equal
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
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G2_equal`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G2Equal where

open import Conformance.Eval
```

## equal-false

```
-- builtin/semantics/bls12_381_G2_equal/equal-false
test-equal-false : Untyped
<<<<<<< HEAD
test-equal-false = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))
=======
test-equal-false = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))))
>>>>>>> origin/master

expected-equal-false : Result
expected-equal-false = success (UCon (tagCon bool false))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-uncompress`.
>>>>>>> origin/master
pending-equal-false : Set
pending-equal-false = Pending (evalRaw test-equal-false ≡ expected-equal-false)
```

## equal-true

```
-- builtin/semantics/bls12_381_G2_equal/equal-true
test-equal-true : Untyped
<<<<<<< HEAD
test-equal-true = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))
=======
test-equal-true = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241")))))
>>>>>>> origin/master

expected-equal-true : Result
expected-equal-true = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-uncompress`.
>>>>>>> origin/master
pending-equal-true : Set
pending-equal-true = Pending (evalRaw test-equal-true ≡ expected-equal-true)
```
