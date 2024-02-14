module PlutusTx.Bool (Bool(..), (&&), (||), not, otherwise) where

{-
We export off-chain Haskell's Bool type as on-chain Plutus's Bool type since they are the same.
-}

import Prelude (Bool (..), otherwise)

{- HLINT ignore -}

{-# INLINE (&&) #-}
-- | Logical AND
--
--   >>> True && False
--   False
--
infixr 3 &&
(&&) :: Bool -> Bool -> Bool
-- See Note [Lazy patterns on function parameters]
(&&) l ~r = if l then r else False

{-# INLINE (||) #-}
-- | Logical OR
--
--   >>> True || False
--   True
--
infixr 2 ||
(||) :: Bool -> Bool -> Bool
(||) l ~r = if l then True else r

{-# INLINABLE not #-}
-- | Logical negation
--
--   >>> not True
--   False
--
not :: Bool -> Bool
not a = if a then False else True

{- Note [Short-circuit evaluation for && and ||]
TLDR: as it stands, the behaviors of `&&` and `||` are inconsistent: they sometimes
short-circuit, sometimes don't.

Function applications in Plutus Tx are strictly evaluated. This includes applications of
`&&` and `||`. There are two problems with this: (1) `&&` and `||` should be made to
short-circuit, otherwise they are not very useful; (2) in fact, their behaviors are
not consistent - sometimes they short-circuit, sometimes they don't!

Why do they short-circuit some of the times, but not always? This is due to the effect
of GHC's inlining. Suppose we run `compile` (which invokes the plugin) in module A:

  - If the module using `&&` is compiled with optimization, and it is an imported
    module (say module B), then module B is compiled first, during which `&&` is likely
    inlined, turning `x && y` into `if x then y else False`, thus enabling short-circuit
    evaluation.
  - If the module using `&&` is compiled without optimization (specifically,
    `-O0 -fmax-simplifier-iteration=0`), then GHC does not inline `&&` and it will not
    short-circuit.
  - If the module using `&&` is module `A` itself, then GHC will not inline `&&` (and thus
    it won't short-circuit) even if module `A` is compiled with optimization. This is
    because the plugin runs before the GHC inliner, and it would have done with
    compiling `&&` before GHC has a chance to inline it.
-}

{- Note [Lazy patterns on function parameters]
In theory, Lazy patterns (~) on function parameters shouldn't make any difference.
This is because function applications in Plutus Tx are strict, so when passing an argument
to a function, the argument will be evaluated immediately, regardless of whether the
corresponding function parameter is lazy or strict. Specifically, both `f !x = body` and
`f ~x = body` in Plutus Tx are compiled into `let f = \x -> body` in PIR:

```
f ~x = body
---> (GHC Core)
f x = body
---> (PIR)
f = \x -> body

f !x = body
---> (GHC Core)
f x = case x@x of { _ -> body }
---> (PIR)
f = \x -> let !x = x in body
---> (PIR inliner)
f = \x -> body
```

It doesn't matter whether or not the function is inlined by the PIR inliner, since the PIR
inliner does not change the semantics of the program.

However, it *does* make a difference if the function is inlined by GHC.
Consider the Plutus Tx code `let f !x = t in f arg`. Here `arg` will be immediately evaluated before
being passed to `f` (as it should). But now consider `let f ~x = t in f arg`. Here GHC
may inline `f`, leading to `t [x := arg]` (recognize that the GHC inliner
also performs beta reduction, in addition to replacing `f` with its definition), where `arg`
may not be evaluated. GHC does so because it is a Haskell compiler and does not know that
Plutus Tx is a strict language.

Therefore, lazy patterns should generally be avoided, since its semantics depend on
what the GHC inliner does. That said, we can use it in some cases to our advantage,
such as in `(&&)` and `(||)`. These logical operators would be much less useful if
they can't short-circuit. Using a lazy pattern on the second parameter helps achieve
the desirable effect, namely, the second parameter is only evaluated if needed, although
this is currently not guaranteed, GHC makes no promise to inline `(&&)` and `(||)`.
To guarantee that the second parameter is only evaluated
when needed, we can potentially use a particular source annotation to tell the PIR
inliner to inline and beta-reduce a function, which would achieve the same effect as if
it is unconditionally inlined by GHC. This is yet to be implemented.
-}
