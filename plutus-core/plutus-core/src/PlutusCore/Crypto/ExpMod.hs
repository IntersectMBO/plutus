{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedSums #-}

module PlutusCore.Crypto.ExpMod
  ( expMod
  ) where

import PlutusCore.Builtin

import GHC.Natural
import GHC.Num.Integer

{-| Modular exponentiation.  This uses GHC.Num.integerPowMod#, which gives the
wrong answer in some cases.  TODO: we'll be able to remove some of the guards
when/if integerPowMod# gets fixed. -}
expMod :: Integer -> Integer -> Natural -> BuiltinResult Natural
expMod b e m
  | m <= 0 = fail "expMod: invalid modulus"
  -- \^ We can't have m<0 when m is a Natural, but we may as well be paranoid.
  | m == 1 = pure 0
  -- \^ Just in case: GHC.Num.Integer.integerRecip# gets this wrong.  Note that 0
  -- is invertible modulo 1, with inverse 0.
  | b == 0 && e < 0 = failNonInvertible 0 m
  -- \^ integerPowMod# incorrectly returns 0 in this case.
  | otherwise =
      case integerPowMod# b e m of
        (# n | #) -> pure n
        (# | () #) -> failNonInvertible b m
  where
    failNonInvertible :: Integer -> Natural -> BuiltinResult Natural
    failNonInvertible b1 m1 =
      fail ("expMod: " ++ (show b1) ++ " is not invertible modulo " ++ (show m1))
{-# INLINE expMod #-}
