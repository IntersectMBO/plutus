{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
module PlutusTx.Code where

import PlutusTx.Coverage
import PlutusTx.Lift.Instances ()

import PlutusIR qualified as PIR

import PlutusCore qualified as PLC
import PlutusCore.Pretty qualified as PLC
import UntypedPlutusCore qualified as UPLC

import Control.Exception
import Flat (Flat (..), unflat)
import Flat.Decoder (DecodeException)

import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import ErrorCode
-- We do not use qualified import because the whole module contains off-chain code
import Prelude as Haskell

-- NOTE: any changes to this type must be paralleled by changes
-- in the plugin code that generates values of this type. That is
-- done by code generation so it's not typechecked normally.
-- | A compiled Plutus Tx program. The last type parameter indicates
-- the type of the Haskell expression that was compiled, and
-- hence the type of the compiled code.
--
-- Note: the compiled PLC program does *not* have normalized types,
-- if you want to put it on the chain you must normalize the types first.
data CompiledCodeIn uni fun a =
    -- | Serialized UPLC code and possibly serialized PIR code with metadata used for program coverage.
    SerializedCode BS.ByteString (Maybe BS.ByteString) CoverageIndex
    -- | Deserialized UPLC program, and possibly deserialized PIR program with metadata used for program coverage.
    | DeserializedCode (UPLC.Program UPLC.NamedDeBruijn uni fun ()) (Maybe (PIR.Program PLC.TyName PLC.Name uni fun ())) CoverageIndex

-- | 'CompiledCodeIn' instantiated with default built-in types and functions.
type CompiledCode = CompiledCodeIn PLC.DefaultUni PLC.DefaultFun

-- | Apply a compiled function to a compiled argument.
applyCode
    :: (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun, uni `PLC.Everywhere` PLC.PrettyConst, PLC.GShow uni, PLC.Pretty fun)
    => CompiledCodeIn uni fun (a -> b) -> CompiledCodeIn uni fun a -> CompiledCodeIn uni fun b
applyCode fun arg = DeserializedCode (UPLC.applyProgram (getPlc fun) (getPlc arg)) (PIR.applyProgram <$> getPir fun <*> getPir arg) (getCovIdx fun <> getCovIdx arg)

-- | The size of a 'CompiledCodeIn', in AST nodes.
sizePlc :: (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun, uni `PLC.Everywhere` PLC.PrettyConst, PLC.GShow uni, PLC.Pretty fun) => CompiledCodeIn uni fun a -> Integer
sizePlc = UPLC.programSize . getPlc

instance (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun, uni `PLC.Everywhere` PLC.PrettyConst, PLC.GShow uni, PLC.Pretty fun)
    => Flat (CompiledCodeIn uni fun a) where
    encode c = encode (getPlc c)

    decode = do
        p <- decode
        pure $ DeserializedCode p Nothing mempty

    size c = size (getPlc c)

{- Note [Deserializing the AST]
The types suggest that we can fail to deserialize the AST that we embedded in the program.
However, we just did it ourselves, so this should be impossible, and we signal this with an
exception.
-}
newtype ImpossibleDeserialisationFailure = ImpossibleDeserialisationFailure DecodeException
    deriving anyclass (Exception)
instance Show ImpossibleDeserialisationFailure where
    show (ImpossibleDeserialisationFailure e) = "Failed to deserialise our own program! This is a bug, please report it. Caused by: " ++ show e

instance HasErrorCode ImpossibleDeserialisationFailure where
      errorCode ImpossibleDeserialisationFailure {} = ErrorCode 40

-- | Get the actual Plutus Core program out of a 'CompiledCodeIn'.
getPlc
    :: (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun, uni `PLC.Everywhere` PLC.PrettyConst, PLC.GShow uni, PLC.Pretty fun)
    => CompiledCodeIn uni fun a -> UPLC.Program UPLC.NamedDeBruijn uni fun ()
getPlc wrapper = case wrapper of
    SerializedCode plc _ _ -> case unflat (BSL.fromStrict plc) of
        Left e  -> throw $ ImpossibleDeserialisationFailure e
        Right p -> p
    DeserializedCode plc _ _ -> plc

-- | Get the Plutus IR program, if there is one, out of a 'CompiledCodeIn'.
getPir
    :: (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun)
    => CompiledCodeIn uni fun a -> Maybe (PIR.Program PIR.TyName PIR.Name uni fun ())
getPir wrapper = case wrapper of
    SerializedCode _ pir _ -> case pir of
        Just bs -> case unflat (BSL.fromStrict bs) of
            Left e  -> throw $ ImpossibleDeserialisationFailure e
            Right p -> Just p
        Nothing -> Nothing
    DeserializedCode _ pir _ -> pir

getCovIdx :: CompiledCodeIn uni fun a -> CoverageIndex
getCovIdx wrapper = case wrapper of
  SerializedCode _ _ idx   -> idx
  DeserializedCode _ _ idx -> idx
