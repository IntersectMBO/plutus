-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}

-- | This module contains example values to be used for testing. These should NOT be used in non-test code!
module PlutusLedgerApi.Test.Examples where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc qualified as PLC
import PlutusCore.Version qualified as PLC
import PlutusLedgerApi.V1
import UntypedPlutusCore qualified as UPLC

import Numeric.Natural
import Universe (Some (Some))

{- Note [Manually constructing scripts]
The scripts we provide here are *manually* constructed Plutus Core. Why not use our great machinery for easily creating
scripts with Plutus Tx? Because Plutus Tx relies on a compiler plugin, and so is always going to be a bit finicky to user.
It seems better therefore to avoid depending on Plutus Tx in any "core" projects like the ledger.
-}

-- | Creates a script which has N arguments, and always succeeds.
alwaysSucceedingNAryFunction :: Natural -> SerialisedScript
alwaysSucceedingNAryFunction n = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 (body n)
  where
    -- No more arguments! The body can be anything that doesn't fail, so we return `\x . x`
    body i | i == 0 = UPLC.LamAbs () (UPLC.DeBruijn 0) $ UPLC.Var () (UPLC.DeBruijn 1)
    -- We're using de Bruijn indices, so we can use the same binder each time!
    body i = UPLC.LamAbs () (UPLC.DeBruijn 0) $ body (i - 1)

-- | Creates a script which has N arguments, and always fails.
alwaysFailingNAryFunction :: Natural -> SerialisedScript
alwaysFailingNAryFunction n = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 (body n)
  where
    -- No more arguments! The body should be error.
    body i | i == 0 = UPLC.Error ()
    -- We're using de Bruijn indices, so we can use the same binder each time!
    body i = UPLC.LamAbs () (UPLC.DeBruijn 0) $ body (i - 1)

summingFunction :: SerialisedScript
summingFunction = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 body
  where
    body = UPLC.Apply () (UPLC.Apply () (UPLC.Builtin () PLC.AddInteger) (PLC.mkConstant @Integer () 1)) (PLC.mkConstant @Integer () 2)

-- | Wrap a script with lambda/app so that, for instance, it has a different hash but the same behavior.
saltFunction :: Integer -> SerialisedScript -> SerialisedScript
saltFunction salt b0 = serialiseUPLC $ UPLC.Program () version body
  where
    UPLC.Program () version b1 = uncheckedDeserialiseUPLC b0

    body =
      UPLC.Apply
        ()
        (UPLC.LamAbs () (UPLC.DeBruijn 0) b1)
        (UPLC.Constant () $ Some $ PLC.ValueOf PLC.DefaultUniInteger salt)

integerToByteStringFunction :: SerialisedScript
integerToByteStringFunction = serialiseUPLC $ UPLC.Program () PLC.plcVersion110 body
  where
    body =
      -- This is run as a Plutus V3 script, so it must return BuiltinUnit
      UPLC.LamAbs () (UPLC.DeBruijn 0) $
        UPLC.Apply
          ()
          (UPLC.LamAbs () (UPLC.DeBruijn 0) (PLC.mkConstant () ()))
          ( PLC.mkIterAppNoAnn
              (UPLC.Builtin () PLC.IntegerToByteString)
              [ PLC.mkConstant @Bool () False
              , PLC.mkConstant @Integer () 5
              , PLC.mkConstant @Integer () 1
              ]
          )
