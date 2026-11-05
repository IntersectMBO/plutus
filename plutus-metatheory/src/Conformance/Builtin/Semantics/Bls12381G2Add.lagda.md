---
title: Conformance.Builtin.Semantics.Bls12381G2Add
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
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G2_add`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G2Add where

open import Conformance.Eval
```

## add

```
-- builtin/semantics/bls12_381_G2_add/add
-- Check that adding two random points on G2 gives the expected result.
test-add : Untyped
<<<<<<< HEAD
test-add = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))))

expected-add : Result
expected-add = success (UCon (tagCon bytestring (mkByteString "b5cf6c76309d98a38950948ce6768309e2e92561762734caaaab65077e1279faff6bba6f9f21bbb3b3fa4ee55aa1332d0f4b3b9a6fa4848e0bf7ae0d38fdc1f1c1908b953ee2b47b88a595b10431acab16522d12a785e27692fc7e0ffa33be07")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
=======
test-add = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*"))))))

expected-add : Result
expected-add = success (UCon (tagCon bytestring (mkByteString "\181\207lv0\157\152\163\137P\148\140\230v\131\t\226\233%av'4\202\170\171e\a~\DC2y\250\255k\186o\159!\187\179\179\250N\229Z\161\&3-\SIK;\154o\164\132\142\v\247\174\r8\253\193\241\193\144\139\149>\226\180{\136\165\149\177\EOT1\172\171\SYNR-\DC2\167\133\226v\146\252~\SI\250\&3\190\a")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
>>>>>>> origin/master
pending-add : Set
pending-add = Pending (evalRaw test-add ≡ expected-add)
```

## add-associative

```
-- builtin/semantics/bls12_381_G2_add/add-associative
-- p+(q+r) = (p+q)+r for three random points on G2.
test-add-associative : Untyped
<<<<<<< HEAD
test-add-associative = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a69d86e011cf692e51ac2031201c27aa06a8f902068fcb98f284d9d925c6502bb0821ba4f49ece3d1db06cd9556f690a117e51df792f7c1d1f5f22b91c3155e9ef2bc43f24ab0a62d8606b3262a117c5635326ae8c9ad897980db6bf4849f903"))))))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a69d86e011cf692e51ac2031201c27aa06a8f902068fcb98f284d9d925c6502bb0821ba4f49ece3d1db06cd9556f690a117e51df792f7c1d1f5f22b91c3155e9ef2bc43f24ab0a62d8606b3262a117c5635326ae8c9ad897980db6bf4849f903"))))))
=======
test-add-associative = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\166\157\134\224\DC1\207i.Q\172 1 \FS'\170\ACK\168\249\STX\ACK\143\203\152\242\132\217\217%\198P+\176\130\ESC\164\244\158\206=\GS\176l\217Uoi\n\DC1~Q\223y/|\GS\US_\"\185\FS1U\233\239+\196?$\171\nb\216`k2b\161\ETB\197cS&\174\140\154\216\151\152\r\182\191HI\249\ETX"))))))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\166\157\134\224\DC1\207i.Q\172 1 \FS'\170\ACK\168\249\STX\ACK\143\203\152\242\132\217\217%\198P+\176\130\ESC\164\244\158\206=\GS\176l\217Uoi\n\DC1~Q\223y/|\GS\US_\"\185\FS1U\233\239+\196?$\171\nb\216`k2b\161\ETB\197cS&\174\140\154\216\151\152\r\182\191HI\249\ETX"))))))
>>>>>>> origin/master

expected-add-associative : Result
expected-add-associative = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
>>>>>>> origin/master
pending-add-associative : Set
pending-add-associative = Pending (evalRaw test-add-associative ≡ expected-add-associative)
```

## add-commutative

```
-- builtin/semantics/bls12_381_G2_add/add-commutative
-- p+q = q+p for two random points in G2.
test-add-commutative : Untyped
<<<<<<< HEAD
test-add-commutative = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))))
=======
test-add-commutative = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))))
>>>>>>> origin/master

expected-add-commutative : Result
expected-add-commutative = success (UCon (tagCon bool true))

<<<<<<< HEAD
-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
=======
-- Pending: bytestring constant; postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
>>>>>>> origin/master
pending-add-commutative : Set
pending-add-commutative = Pending (evalRaw test-add-commutative ≡ expected-add-commutative)
```

## add-zero

```
-- builtin/semantics/bls12_381_G2_add/add-zero
-- Adding the zero element to a random point doesn't change it.
test-add-zero : Untyped
<<<<<<< HEAD
test-add-zero = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))))

expected-add-zero : Result
expected-add-zero = success (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
=======
test-add-zero = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))))

expected-add-zero : Result
expected-add-zero = success (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
>>>>>>> origin/master
pending-add-zero : Set
pending-add-zero = Pending (evalRaw test-add-zero ≡ expected-add-zero)
```
