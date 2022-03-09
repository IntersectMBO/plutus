{-# LANGUAGE TypeApplications #-}
{-|
This module contains example values to be used for testing. These should NOT be used in non-test code!
-}
module Plutus.V1.Ledger.Examples (alwaysSucceedingNAryFunction, alwaysFailingNAryFunction, summingFunction, saltFunction) where

import Codec.Serialise
import Data.ByteString.Lazy (fromStrict, toStrict)
import Data.ByteString.Short
import Numeric.Natural
import Plutus.V1.Ledger.Api
import Plutus.V1.Ledger.Scripts qualified as Scripts
import PlutusCore qualified as PLC
import PlutusCore.MkPlc qualified as PLC
import Universe (Some (Some))
import UntypedPlutusCore qualified as UPLC

{- Note [Manually constructing scripts]
The scripts we provide here are *manually* constructed Plutus Core. Why not use our great machinery for easily creating
scripts with Plutus Tx? Because Plutus Tx relies on a compiler plugin, and so is always going to be a bit finicky to user.
It seems better therefore to avoid depending on Plutus Tx in any "core" projects like the ledger.
-}

-- | Creates a script which has N arguments, and always succeeds.
alwaysSucceedingNAryFunction :: Natural -> SerializedScript
alwaysSucceedingNAryFunction n = toShort $ toStrict $ serialise $ Scripts.Script $ UPLC.Program () (PLC.defaultVersion ()) (body n)
    where
        -- No more arguments! The body can be anything that doesn't fail, so we return `\x . x`
        body i | i == 0 = UPLC.LamAbs() (UPLC.DeBruijn 0) $ UPLC.Var () (UPLC.DeBruijn 1)
        -- We're using de Bruijn indices, so we can use the same binder each time!
        body i = UPLC.LamAbs () (UPLC.DeBruijn 0) $ body (i-1)

-- | Creates a script which has N arguments, and always fails.
alwaysFailingNAryFunction :: Natural -> SerializedScript
alwaysFailingNAryFunction n = toShort $ toStrict $ serialise $ Scripts.Script $ UPLC.Program () (PLC.defaultVersion ()) (body n)
    where
        -- No more arguments! The body should be error.
        body i | i == 0 = UPLC.Error ()
        -- We're using de Bruijn indices, so we can use the same binder each time!
        body i = UPLC.LamAbs () (UPLC.DeBruijn 0) $ body (i-1)

summingFunction :: SerializedScript
summingFunction = toShort $ toStrict $ serialise $ Scripts.Script $ UPLC.Program () (PLC.defaultVersion ()) body
    where
        body = UPLC.Apply () (UPLC.Apply () (UPLC.Builtin () PLC.AddInteger) (PLC.mkConstant @Integer () 1)) (PLC.mkConstant @Integer () 2)

-- | Wrap a script with lambda/app so that, for instance, it has a different hash but the same behavior.
saltFunction :: Integer -> SerializedScript -> SerializedScript
saltFunction salt b0 = toShort $ toStrict $ serialise $ Scripts.Script $ UPLC.Program () version body
    where
        Scripts.Script (UPLC.Program () version b1) = deserialise $ fromStrict $ fromShort b0

        body = UPLC.Apply ()
            (UPLC.LamAbs () (UPLC.DeBruijn 0) b1)
            (UPLC.Constant () $ Some $ PLC.ValueOf PLC.DefaultUniInteger salt)
