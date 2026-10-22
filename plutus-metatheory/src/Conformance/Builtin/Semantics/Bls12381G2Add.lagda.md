---
title: Conformance.Builtin.Semantics.Bls12381G2Add
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
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
test-add = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))))

expected-add : Result
expected-add = success (UCon (tagCon bytestring (mkByteString "b5cf6c76309d98a38950948ce6768309e2e92561762734caaaab65077e1279faff6bba6f9f21bbb3b3fa4ee55aa1332d0f4b3b9a6fa4848e0bf7ae0d38fdc1f1c1908b953ee2b47b88a595b10431acab16522d12a785e27692fc7e0ffa33be07")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
pending-add : Set
pending-add = Pending (evalRaw test-add ≡ expected-add)
```

## add-associative

```
-- builtin/semantics/bls12_381_G2_add/add-associative
-- p+(q+r) = (p+q)+r for three random points on G2.
test-add-associative : Untyped
test-add-associative = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a69d86e011cf692e51ac2031201c27aa06a8f902068fcb98f284d9d925c6502bb0821ba4f49ece3d1db06cd9556f690a117e51df792f7c1d1f5f22b91c3155e9ef2bc43f24ab0a62d8606b3262a117c5635326ae8c9ad897980db6bf4849f903"))))))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "a69d86e011cf692e51ac2031201c27aa06a8f902068fcb98f284d9d925c6502bb0821ba4f49ece3d1db06cd9556f690a117e51df792f7c1d1f5f22b91c3155e9ef2bc43f24ab0a62d8606b3262a117c5635326ae8c9ad897980db6bf4849f903"))))))

expected-add-associative : Result
expected-add-associative = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
pending-add-associative : Set
pending-add-associative = Pending (evalRaw test-add-associative ≡ expected-add-associative)
```

## add-commutative

```
-- builtin/semantics/bls12_381_G2_add/add-commutative
-- p+q = q+p for two random points in G2.
test-add-commutative : Untyped
test-add-commutative = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))))

expected-add-commutative : Result
expected-add-commutative = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
pending-add-commutative : Set
pending-add-commutative = Pending (evalRaw test-add-commutative ≡ expected-add-commutative)
```

## add-zero

```
-- builtin/semantics/bls12_381_G2_add/add-zero
-- Adding the zero element to a random point doesn't change it.
test-add-zero : Untyped
test-add-zero = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))))

expected-add-zero : Result
expected-add-zero = success (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
pending-add-zero : Set
pending-add-zero = Pending (evalRaw test-add-zero ≡ expected-add-zero)
```
