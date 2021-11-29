{-# LANGUAGE FlexibleContexts #-}
module PlutusTx.LiftU (module LiftU, liftProgram, liftProgramDef) where

import PlutusTx.LiftU.Class as LiftU
import PlutusTx.LiftU.Instances ()
import PlutusTx.LiftU.TH as LiftU

import PlutusCore qualified as PLC
import UntypedPlutusCore qualified as UPLC

import Prelude

-- | Get a Plutus Core program corresponding to the given value.
liftProgram
    :: (LiftU.LiftU name uni fun a)
    => a -> UPLC.Program name uni fun ()
liftProgram x = UPLC.Program () (PLC.defaultVersion ()) $ liftU x

-- | Get a Plutus Core program in the default universe corresponding to the given value.
liftProgramDef
    :: LiftU.LiftU UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun a
    => a -> UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
liftProgramDef = liftProgram
