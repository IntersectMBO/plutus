---
title: Conformance.Builtin.Semantics.Bls12381MillerLoop
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_millerLoop`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381MillerLoop where

open import Conformance.Eval
```

## balanced

```
-- builtin/semantics/bls12_381_millerLoop/balanced
-- <np,q> = <p,nq>
test-balanced : Untyped
test-balanced = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 251123)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5")))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 251123)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))))

expected-balanced : Result
expected-balanced = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`; postulated builtin `bls12-381-G2-scalarMul`.
pending-balanced : Set
pending-balanced = Pending (evalRaw test-balanced ≡ expected-balanced)
```

## equal-pairing

```
-- builtin/semantics/bls12_381_millerLoop/equal-pairing
-- Check that applying finalVerify to the same two points in GT returns True.
test-equal-pairing : Untyped
test-equal-pairing = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))))

expected-equal-pairing : Result
expected-equal-pairing = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-equal-pairing : Set
pending-equal-pairing = Pending (evalRaw test-equal-pairing ≡ expected-equal-pairing)
```

## left-additive

```
-- builtin/semantics/bls12_381_millerLoop/left-additive
-- <p1+p2,q> = <p1,q><p2,q>
test-left-additive : Untyped
test-left-additive = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))) (UApp (UApp (UBuiltin bls12-381-mulMlResult) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))))

expected-left-additive : Result
expected-left-additive = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`; postulated builtin `bls12-381-mulMlResult`.
pending-left-additive : Set
pending-left-additive = Pending (evalRaw test-left-additive ≡ expected-left-additive)
```

## random-pairing

```
-- builtin/semantics/bls12_381_millerLoop/random-pairing
-- Check that the results of two millerLoops of random points are different.
test-random-pairing : Untyped
test-random-pairing = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))))

expected-random-pairing : Result
expected-random-pairing = success (UCon (tagCon bool false))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-uncompress`.
pending-random-pairing : Set
pending-random-pairing = Pending (evalRaw test-random-pairing ≡ expected-random-pairing)
```

## right-additive

```
-- builtin/semantics/bls12_381_millerLoop/right-additive
-- <p,q1+q2> = <p,q1><p,q2>
test-right-additive : Untyped
test-right-additive = (UApp (UApp (UBuiltin bls12-381-finalVerify) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a"))))))) (UApp (UApp (UBuiltin bls12-381-mulMlResult) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "b0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1")))))) (UApp (UApp (UBuiltin bls12-381-millerLoop) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a")))))))

expected-right-additive : Result
expected-right-additive = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-finalVerify`; postulated builtin `bls12-381-millerLoop`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`; postulated builtin `bls12-381-mulMlResult`.
pending-right-additive : Set
pending-right-additive = Pending (evalRaw test-right-additive ≡ expected-right-additive)
```
