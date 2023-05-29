-- editorconfig-checker-disable-file
{-# LANGUAGE TemplateHaskell #-}
module PlutusTx (
    module Export,
    CompiledCode,
    CompiledCodeIn,
    getPlc,
    getPlcNoAnn,
    getPir,
    getPirNoAnn,
    applyCode,
    unsafeApplyCode,
    BuiltinData,
    Data (..),
    ToData (..),
    FromData (..),
    UnsafeFromData (..),
    toData,
    fromData,
    builtinDataToData,
    dataToBuiltinData,
    unstableMakeIsData,
    makeIsDataIndexed,
    Lift,
    Typeable,
    makeLift,
    safeLiftCode,
    liftCode,
    liftCodeDef) where

import PlutusCore.Data (Data (..))
import PlutusTx.Builtins (BuiltinData, builtinDataToData, dataToBuiltinData)
import PlutusTx.Code (CompiledCode, CompiledCodeIn, applyCode, getPir, getPirNoAnn, getPlc,
                      getPlcNoAnn, unsafeApplyCode)
import PlutusTx.IsData (FromData (..), ToData (..), UnsafeFromData (..), fromData,
                        makeIsDataIndexed, toData, unstableMakeIsData)
import PlutusTx.Lift (liftCode, liftCodeDef, makeLift, safeLiftCode)
import PlutusTx.Lift.Class (Lift, Typeable)
import PlutusTx.TH as Export

import Data.ByteString.Lazy qualified as BSL
import Flat (unflat)
import PlutusTx.Builtins (Integer)
import PlutusTx.Code (CompiledCodeIn (SerializedCode))
import Prelude (Either (..))
import UntypedPlutusCore qualified as UPLC

-- MAKE SURE TO CHANGE THE ABSOLUTE PATH TO THE ONE VALID ON YOUR MACHINE
compiledMyScript :: CompiledCode (Integer -> Integer)
compiledMyScript = $$(loadFromFile "/home/effectfully/code/iohk/plutus/addInteger16.flat-namedDeBruijn")

deserialized :: UPLC.Program UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
Right (UPLC.UnrestrictedProgram deserialized) = unflat (BSL.fromStrict bs) where
    SerializedCode bs _ _ = compiledMyScript

-- >>> import PlutusCore.Pretty
-- >>> pretty deserialized
-- (program 2.0.0 (lam i_0 [ [ (builtin addInteger) (con integer 16) ] i_0 ]))
