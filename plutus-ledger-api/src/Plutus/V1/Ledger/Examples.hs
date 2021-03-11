{-# LANGUAGE TypeApplications #-}
{-|
This module contains example values to be used for testing. These should NOT be used in non-test code!
-}
module Plutus.V1.Ledger.Examples where

import           Data.ByteString.Short
import qualified Flat
import           Numeric.Natural
import           Plutus.V1.Ledger.Api
import qualified Plutus.V1.Ledger.Scripts as Scripts
import qualified PlutusCore               as PLC
import qualified UntypedPlutusCore        as UPLC

{- Note [Manually constructing scripts]
The scripts we provide here are *manually* constructed Plutus Core. Why not use our great machinery for easily creating
scripts with Plutus Tx? Because Plutus Tx relies on a compiler plugin, and so is always going to be a bit finicky to user.
It seems better therefore to avoid depending on Plutus Tx in any "core" projects like the ledger.
-}

-- | Creates a script which has N arguments, and always succeeds.
alwaysSucceedingNAryFunction :: Natural -> Script
alwaysSucceedingNAryFunction n = toShort $ Flat.flat @Scripts.Script $ Scripts.Script $ UPLC.Program () (PLC.defaultVersion ()) (body n)
    where
        -- No more arguments! The body can be anything that doesn't fail, so we return `\x . x`
        body i | i == 0 = UPLC.LamAbs() (UPLC.DeBruijn 0) $ UPLC.Var () (UPLC.DeBruijn 1)
        -- We're using de Bruijn indices, so we can use the same binder each time!
        body i = UPLC.LamAbs () (UPLC.DeBruijn 0) $ body (i-1)

-- | Creates a script which has N arguments, and always fails.
alwaysFailingNAryFunction :: Natural -> Script
alwaysFailingNAryFunction n = toShort $ Flat.flat @Scripts.Script $ Scripts.Script $ UPLC.Program () (PLC.defaultVersion ()) (body n)
    where
        -- No more arguments! The body should be error.
        body i | i == 0 = UPLC.Error ()
        -- We're using de Bruijn indices, so we can use the same binder each time!
        body i = UPLC.LamAbs () (UPLC.DeBruijn 0) $ body (i-1)
