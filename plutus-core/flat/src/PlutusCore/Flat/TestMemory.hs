{-|
Represent a data type in memory using the flat representation.

Access it as normal using pattern synonyms (https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pattern_synonyms.html) or lenses?

This should:
* massively reduce memory usage (without requiring any manual specialisation)
* possibly reduce traversal times (via better caching) -}
module PlutusCore.Flat.TestMemory where

import Data.ByteString

import PlutusCore.Flat

{-
>>> fact fact 3
3 * fact fact 2 = 3 * 2 * 1
-}
-- x :: Int -> Int
x n = fact (fact n)

fact :: (Int -> Int) -> Int -> Int
fact _ 1 = 1
fact k n = n * k (n - 1)
