{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusCore.Generators.PIR.GenerateKinds where

import Test.QuickCheck.GenT

import PlutusCore.Generators.PIR.Common
import PlutusIR

import PlutusCore.Generators.PIR.GenTm

-- | Shriking-order on kinds.
--
-- A kind `k1 = foldr (->) * ks1` is less than or equal to a kind `k2 = foldr (->) * ks2`
-- when `ks1` can be constructed by dropping and shrinking kinds in `ks2`.
--
-- This shrinking order means that `* -> (* -> * -> * -> *) -> *` can shrink to
-- `* -> *` or `* -> (* -> *) -> *` but not to `* -> * -> * -> *`. Not allowing
-- this final shrink is important as we are guaranteed to only ever reduce the
-- number of type arguments we need to provide when shrinking - thus allowing us
-- to guarantee that e.g. generated datatypes never increase their number of
-- parameters. This restriction is important because once the number of parameters
-- starts to grow during shrinking it is difficult to ensure that the size of
-- generated types and terms doesn't baloon and cause a shrink-loop.
leKind :: Kind () -> Kind () -> Bool
leKind k1 k2 = go (reverse $ argsKind k1) (reverse $ argsKind k2)
  where
    go [] _                = True
    go _ []                = False
    go (k : ks) (k' : ks')
      | leKind k k' = go ks ks'
      | otherwise   = go (k : ks) ks'

-- | Strict shrinking order on kinds
ltKind :: Kind () -> Kind () -> Bool
ltKind k k' = k /= k' && leKind k k'

instance Arbitrary (Kind ()) where
  arbitrary = sized $ arb . (`div` 3)
    where
      arb 0 = pure $ Star
      arb n = frequency [(4, pure $ Star),
                         (1, (:->) <$> arb (div n 6) <*> arb (div (5 * n) 6))]
  shrink Star      = []
  shrink (a :-> b) = [b] ++ [a' :-> b' | (a', b') <- shrink (a, b)]
    -- Note: `a` can have bigger arity than `a -> b` so don't shrink to it!
