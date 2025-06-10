{-# LANGUAGE MagicHash   #-}
{-# LANGUAGE UnboxedSums #-}

module TestIPM where

import GHC.Natural
import GHC.Num.Integer
import GHC.Num.Natural

-- Wrappers to make things easier in ghci
integerPowMod :: Integer -> Integer -> Natural -> Maybe Natural
integerPowMod b e m =
  case integerPowMod# b e m of
    (# n | #)  -> Just n
    (# | () #) -> Nothing

integerRecip :: Integer -> Natural -> Maybe Natural
integerRecip b m =
  case integerRecipMod# b m of
    (# n | #)  -> Just n
    (# | () #) -> Nothing

