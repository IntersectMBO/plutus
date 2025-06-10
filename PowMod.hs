{-# LANGUAGE MagicHash   #-}
{-# LANGUAGE UnboxedSums #-}

module PowMod
where

import GHC.Natural
import GHC.Num.Integer

powMod :: Integer -> Integer -> Natural -> Maybe Natural
powMod b e m =
    case integerPowMod# b e m of
      (# | () #) -> Nothing
      (# n | #)  -> Just n
