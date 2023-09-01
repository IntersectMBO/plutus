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

However, it *does* make a difference if the function is unconditionally inlined by GHC.
Consider the Plutus Tx code `let f !x = t in f arg`. Here `arg` will be immediately evaluated before
being passed to `f` (as it should). But now consider `let f ~x = t in f arg`. Here GHC
may unconditionally inline `f`, leading to `t [x := arg]` (recognize that the GHC inliner
also performs beta reduction, in addition to replacing `f` with its definition), where `arg`
may not be evaluated. GHC does so because it is a Haskell compiler and does not know that
Plutus Tx is a strict language.

Therefore, lazy patterns should generally be avoided, since its semantics depend on
what the GHC inliner does. That said, we can use it in some cases to our advantage,
such as in `(&&)` and `(||)`. These logical operators would be much less useful if
they can't short-circuit. Using a lazy pattern on the second parameter helps achieve
the desirable effect, namely, the second parameter is only evaluated if needed, although
this is currently not guaranteed, since `(&&)` and `(||)` are not necessarily
unconditionally inlined by GHC. To guarantee that the second parameter is only evaluated
when needed, we can potentially use a particular source annotation to tell the PIR
inliner to inline and beta-reduce a function, which would achieve the same effect as if
it is unconditionally inlined by GHC. This is yet to be implemented.
-}
