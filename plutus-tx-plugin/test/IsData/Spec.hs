{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-context #-}
module IsData.Spec where

import           Common
import           Lib
import           PlcTestUtils
import           Plugin.Data.Spec
import           Plugin.Primitives.Spec

import qualified PlutusTx.Builtins      as Builtins
import           PlutusTx.Code
import qualified PlutusTx.IsData        as IsData
import           PlutusTx.Plugin
import qualified PlutusTx.Prelude       as P

import qualified PlutusCore             as PLC
import qualified PlutusCore.MkPlc       as PLC
import qualified UntypedPlutusCore      as UPLC

import           Data.Proxy

IsData.unstableMakeIsData ''MyMonoData
IsData.unstableMakeIsData ''MyMonoRecord
IsData.unstableMakeIsData ''MyPolyData

data NestedRecord = NestedRecord { unNested :: Maybe (Integer, Integer) }
IsData.unstableMakeIsData ''NestedRecord

instance P.Eq NestedRecord where
    {-# INLINABLE (==) #-}
    (NestedRecord i1) == (NestedRecord i2) = i1 P.== i2

data WrappedBS = WrappedBS { unWrap :: Builtins.BuiltinByteString }
IsData.unstableMakeIsData ''WrappedBS

instance P.Eq WrappedBS where
    {-# INLINABLE (==) #-}
    (WrappedBS i1) == (WrappedBS i2) = i1 P.== i2

deconstructData :: CompiledCode (Builtins.BuiltinData -> Maybe (Integer, Integer))
deconstructData = plc (Proxy @"deconstructData4") (\(d :: Builtins.BuiltinData) -> IsData.fromBuiltinData d)

unsafeDeconstructData :: CompiledCode (Builtins.BuiltinData -> Maybe (Integer, Integer))
unsafeDeconstructData = plc (Proxy @"deconstructData4") (\(d :: Builtins.BuiltinData) -> IsData.unsafeFromBuiltinData d)

{-# INLINABLE isDataRoundtrip #-}
isDataRoundtrip :: (IsData.FromData a, IsData.UnsafeFromData a, IsData.ToData a, P.Eq a) => a -> Bool
isDataRoundtrip a =
    let d = IsData.toBuiltinData a
        safeRoundtrip = case IsData.fromBuiltinData d of
            Just a' -> a P.== a'
            Nothing -> False
        unsafeRoundtrip = IsData.unsafeFromBuiltinData d P.== a
    in safeRoundtrip && unsafeRoundtrip

tests :: TestNested
tests = testNested "IsData" [
    goldenUEval "int" [plc (Proxy @"int") (isDataRoundtrip (1::Integer))]
    , goldenUEval "tuple" [plc (Proxy @"tuple") (isDataRoundtrip (1::Integer, 2::Integer))]
    , goldenUEval "tupleInterop" [
            getPlc (plc (Proxy @"tupleInterop") (\(d :: P.BuiltinData) -> case IsData.fromBuiltinData d of { Just t -> t P.== (1::Integer, 2::Integer); Nothing -> False}))
            , UPLC.Program () (PLC.defaultVersion ()) (PLC.mkConstant () (IsData.toData (1::Integer, 2::Integer)))]
    , goldenUEval "unsafeTupleInterop" [
            getPlc (plc (Proxy @"unsafeTupleInterop") (\(d :: P.BuiltinData) -> IsData.unsafeFromBuiltinData d P.== (1::Integer, 2::Integer)))
            , UPLC.Program () (PLC.defaultVersion ()) (PLC.mkConstant () (IsData.toData (1::Integer, 2::Integer)))]
    , goldenUEval "unit" [plc (Proxy @"unit") (isDataRoundtrip ())]
    , goldenUEval "unitInterop" [
            getPlc (plc (Proxy @"unitInterop") (\(d :: P.BuiltinData) -> case IsData.fromBuiltinData d of { Just t -> t P.== (); Nothing -> False}))
            , UPLC.Program () (PLC.defaultVersion ()) (PLC.mkConstant () (IsData.toData ()))]
    , goldenUEval "mono" [plc (Proxy @"mono") (isDataRoundtrip (Mono2 2))]
    , goldenUEval "poly" [plc (Proxy @"poly") (isDataRoundtrip (Poly1 (1::Integer) (2::Integer)))]
    , goldenUEval "record" [plc (Proxy @"record") (isDataRoundtrip (MyMonoRecord 1 2))]
    , goldenUEval "list" [plc (Proxy @"list") (isDataRoundtrip ([1]::[Integer]))]
    , goldenUEval "nested" [plc (Proxy @"nested") (isDataRoundtrip (NestedRecord (Just (1, 2))))]
    , goldenUEval "bytestring" [plc (Proxy @"bytestring") (isDataRoundtrip (WrappedBS Builtins.emptyByteString))]
    , goldenPir "deconstructData" deconstructData
    , goldenPir "unsafeDeconstructData" unsafeDeconstructData
  ]
