{-# LANGUAGE CPP         #-}
{-# LANGUAGE MagicHash   #-}
{-# LANGUAGE UnboxedSums #-}
module PlutusCore.Crypto.ExpMod
    ( expMod
    ) where

import PlutusCore.Builtin

import GHC.Natural
import GHC.Num.Integer

-- similar to `Default.Builtins.nonZeroSecondArg`
-- We don't really need it because integerPowMod# returns `()` on zero mod, but we put
-- in case of future implementation changes.
expMod _ _ 0 = fail "Cannot divide by zero"
expMod b e m =
    case integerPowMod# b e m of
        (# n | #)  -> pure n
        (# | () #) -> fail "expMod: failure"


expMod :: Integer -> Integer -> Natural -> BuiltinResult Natural
{-# INLINE expMod #-}
