---
title: Conformance.Builtin.Semantics.Bls12381G2Equal
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
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
test-equal-false = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))

expected-equal-false : Result
expected-equal-false = success (UCon (tagCon bool false))

-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-uncompress`.
pending-equal-false : Set
pending-equal-false = Pending (evalRaw test-equal-false ≡ expected-equal-false)
```

## equal-true

```
-- builtin/semantics/bls12_381_G2_equal/equal-true
test-equal-true : Untyped
test-equal-true = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))

expected-equal-true : Result
expected-equal-true = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-uncompress`.
pending-equal-true : Set
pending-equal-true = Pending (evalRaw test-equal-true ≡ expected-equal-true)
```
