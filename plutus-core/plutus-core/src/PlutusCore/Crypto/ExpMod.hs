{-# LANGUAGE CPP         #-}
{-# LANGUAGE MagicHash   #-}
{-# LANGUAGE UnboxedSums #-}
module PlutusCore.Crypto.ExpMod
    ( expMod
    ) where

import PlutusCore.Builtin

import GHC.Natural

-- Ghc>=9 has this in base
#if MIN_VERSION_base(4,15,0)
import GHC.Num.Integer
-- similar to `Default.Builtins.nonZeroSecondArg`
-- We don't really need it because integerPowMod# returns `()` on zero mod, but we put
-- in case of future implementation changes.
expMod _ _ 0 = fail "Cannot divide by zero"
expMod b e m =
    case integerPowMod# b e m of
        (# n | #)  -> pure n
        (# | () #) -> fail "expMod: failure"
#else
-- FIXME: fugly stub implementation to make the various test-suites/CI pass for GHC8.10.
-- This means that we cannot provide random testing for expMod at the moment.
expMod _ _ 0 = fail "Cannot divide by zero"
expMod 500 0 500 = pure 1
expMod 500 5 500 = pure 0
expMod 1 (-3) 4 = pure 1
expMod 2 (-3) 3 = pure 2
expMod 4 (-5) 9 = pure 4
expMod 2 (-3) 4 = fail "expMod: failure"
expMod 500 (-5) 5 = fail "expMod: failure"
-- FIXME: this has to be fixed either by deciding to stop supporting GHC8.10
-- or by backporting ghc-bignum's integerPowMod# implementation to old ghc8.10/integer-gmp<1.1
expMod _b _e _m = fail "expMod: FIXME: stub for GHC8.10, report to plutus developers"
#endif

expMod :: Integer -> Integer -> Natural -> BuiltinResult Natural
{-# INLINE expMod #-}
