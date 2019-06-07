{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE ViewPatterns       #-}
module Language.PlutusTx.Code where

import qualified Language.PlutusTx.Lift.Class as Lift

import qualified Language.PlutusIR            as PIR
import qualified Language.PlutusIR.MkPir      as PIR

import qualified Language.PlutusCore          as PLC

import           Codec.Serialise              (DeserialiseFailure, deserialiseOrFail)
import           Control.Exception

import qualified Data.ByteString              as BS
import qualified Data.ByteString.Lazy         as BSL

-- NOTE: any changes to this type must be paralleled by changes
-- in the plugin code that generates values of this type. That is
-- done by code generation so it's not typechecked normally.
-- | A compiled Plutus Tx program. The type parameter indicates
-- the type of the Haskell expression that was compiled, and
-- hence the type of the compiled code.
--
-- Note: the compiled PLC program does *not* have normalized types,
-- if you want to put it on the chain you must normalize the types first.
data CompiledCode a =
    -- | Serialized PLC code and possibly serialized PIR code.
    SerializedCode BS.ByteString (Maybe BS.ByteString)
    -- | Deserialized PLC program and possibly deserialized PIR program.
    | DeserializedCode (PLC.Program PLC.TyName PLC.Name ()) (Maybe (PIR.Program PLC.TyName PLC.Name ()))

-- Note that we do *not* have a TypeablePlc instance, since we don't know what the type is. We could in principle store it after the plugin
-- typechecks the code, but we don't currently.
instance Lift.Lift (CompiledCode a) where
    lift (getPlc -> (PLC.Program () _ body)) = PIR.embed <$> PLC.rename body

-- | Apply a compiled function to a compiled argument.
applyCode :: CompiledCode (a -> b) -> CompiledCode a -> CompiledCode b
applyCode fun arg = DeserializedCode (getPlc fun `PLC.applyProgram` getPlc arg) Nothing

-- | The size of a 'CompiledCode', in AST nodes.
sizePlc :: CompiledCode a -> Integer
sizePlc = PLC.programSize . getPlc

{- Note [Deserializing the AST]
The types suggest that we can fail to deserialize the AST that we embedded in the program.
However, we just did it ourselves, so this should be impossible, and we signal this with an
exception.
-}
newtype ImpossibleDeserialisationFailure = ImpossibleDeserialisationFailure DeserialiseFailure
instance Show ImpossibleDeserialisationFailure where
    show (ImpossibleDeserialisationFailure e) = "Failed to deserialise our own program! This is a bug, please report it. Caused by: " ++ show e
instance Exception ImpossibleDeserialisationFailure

-- | Get the actual Plutus Core program out of a 'CompiledCode'.
getPlc :: CompiledCode a -> PLC.Program PLC.TyName PLC.Name ()
getPlc wrapper = case wrapper of
    SerializedCode plc _ -> case deserialiseOrFail (BSL.fromStrict plc) of
        Left e  -> throw $ ImpossibleDeserialisationFailure e
        Right p -> p
    DeserializedCode plc _ -> plc

-- | Get the Plutus IR program, if there is one, out of a 'CompiledCode'.
getPir :: CompiledCode a -> Maybe (PIR.Program PIR.TyName PIR.Name ())
getPir wrapper = case wrapper of
    SerializedCode _ pir -> case pir of
        Just bs -> case deserialiseOrFail (BSL.fromStrict bs) of
            Left e  -> throw $ ImpossibleDeserialisationFailure e
            Right p -> Just p
        Nothing -> Nothing
    DeserializedCode _ pir -> pir
