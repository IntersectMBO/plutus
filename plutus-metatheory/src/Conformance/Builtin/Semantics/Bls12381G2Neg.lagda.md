---
title: Conformance.Builtin.Semantics.Bls12381G2Neg
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

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
test-add-neg = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-neg) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))))

expected-add-neg : Result
expected-add-neg = success (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`; postulated builtin `bls12-381-G2-neg`.
pending-add-neg : Set
pending-add-neg = Pending (evalRaw test-add-neg ≡ expected-add-neg)
```

## neg

```
-- builtin/semantics/bls12_381_G2_neg/neg
-- Check that hashing a random bytestring gives the expected result.
test-neg : Untyped
test-neg = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-neg) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))))

expected-neg : Result
expected-neg = success (UCon (tagCon bytestring (mkByteString "a310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-neg`; postulated builtin `bls12-381-G2-uncompress`.
pending-neg : Set
pending-neg = Pending (evalRaw test-neg ≡ expected-neg)
```

## neg-zero

```
-- builtin/semantics/bls12_381_G2_neg/neg-zero
-- The negative of the zero point is the zero point.
test-neg-zero : Untyped
test-neg-zero = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UBuiltin bls12-381-G2-neg) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))))

expected-neg-zero : Result
expected-neg-zero = success (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

-- Pending: postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-neg`; postulated builtin `bls12-381-G2-uncompress`.
pending-neg-zero : Set
pending-neg-zero = Pending (evalRaw test-neg-zero ≡ expected-neg-zero)
```
