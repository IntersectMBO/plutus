-- |
-- Module      : Foundation.Strict
-- License     : BSD-style
-- Maintainer  : Foundation
-- Stability   : stable
-- Portability : portable
--
-- Enforce strictness when executing lambda
--

module Foundation.Strict
    ( strict1
    , strict2
    , strict3
    , strict4
    , strict5
    , strict6
    ) where

strict1 :: (a -> b) -> a -> b
strict1 f !a = f a

strict2 :: (a -> b -> c) -> a -> b -> c
strict2 f !a !b = f a b

strict3 :: (a -> b -> c -> d) -> a -> b -> c -> d
strict3 f !a !b !c = f a b c

strict4 :: (a -> b -> c -> d -> e) -> a -> b -> c -> d -> e
strict4 f !a !b !c !d = f a b c d

strict5 :: (a -> b -> c -> d -> e -> f) -> a -> b -> c -> d -> e -> f
strict5 f !a !b !c !d !e = f a b c d e

strict6 :: (a -> b -> c -> d -> e -> f -> g) -> a -> b -> c -> d -> e -> f -> g
strict6 f !a !b !c !d !e !g = f a b c d e g

