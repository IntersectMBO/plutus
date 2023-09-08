-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}

module IsData.Spec where

import Test.Tasty.Extras

import Plugin.Data.Spec

import PlutusCore.Test
import PlutusTx.AsData qualified as AsData
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.IsData qualified as IsData
import PlutusTx.Plugin
import PlutusTx.Prelude qualified as P
import PlutusTx.Test

import PlutusCore qualified as PLC
import PlutusCore.MkPlc qualified as PLC
import UntypedPlutusCore qualified as UPLC

import Data.Proxy

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

AsData.asData [d|
  data SecretlyData = FirstC () | SecondC Integer
     deriving newtype (P.Eq, IsData.FromData, IsData.UnsafeFromData, IsData.ToData)
  |]

AsData.asData [d|
  data RecordConstructor a = RecordConstructor { x :: a, y :: Integer }
  |]

AsData.asData [d|
  data MaybeD a = JustD a | NothingD
  |]

-- Features a nested field which is also defined with AsData
matchAsData :: CompiledCode (MaybeD SecretlyData -> SecretlyData)
matchAsData = plc (Proxy @"matchAsData") (
  \case
    JustD a  -> a
    NothingD -> FirstC ())

recordAsData :: CompiledCode (RecordConstructor Integer)
recordAsData = plc (Proxy @"recordAsData") (RecordConstructor 1 2)

dataToData :: CompiledCode (RecordConstructor Integer -> SecretlyData)
dataToData = plc (Proxy @"dataToData")
  (\case
      RecordConstructor a b | a P.== 3, b P.== 4 -> SecondC (Builtins.addInteger a b)
      _                                          -> FirstC ()
  )

-- Should ultimately use equalsData
equalityAsData :: CompiledCode (SecretlyData -> SecretlyData -> Bool)
equalityAsData = plc (Proxy @"equalityAsData") (\x y -> x P.== y)

fieldAccessor :: CompiledCode (RecordConstructor Integer -> Integer)
fieldAccessor = plc (Proxy @"fieldAccessor") (\r -> x r)

tests :: TestNested
tests = testNestedGhc "IsData" [
    goldenUEval "int" [plc (Proxy @"int") (isDataRoundtrip (1::Integer))]
    , goldenUEval "tuple" [plc (Proxy @"tuple") (isDataRoundtrip (1::Integer, 2::Integer))]
    , goldenUEval "tupleInterop" [
            getPlcNoAnn (plc (Proxy @"tupleInterop") (\(d :: P.BuiltinData) -> case IsData.fromBuiltinData d of { Just t -> t P.== (1::Integer, 2::Integer); Nothing -> False}))
            , UPLC.Program () (PLC.latestVersion) (PLC.mkConstant () (IsData.toData (1::Integer, 2::Integer)))]
    , goldenUEval "unsafeTupleInterop" [
            getPlcNoAnn (plc (Proxy @"unsafeTupleInterop") (\(d :: P.BuiltinData) -> IsData.unsafeFromBuiltinData d P.== (1::Integer, 2::Integer)))
            , UPLC.Program () (PLC.latestVersion) (PLC.mkConstant () (IsData.toData (1::Integer, 2::Integer)))]
    , goldenUEval "unit" [plc (Proxy @"unit") (isDataRoundtrip ())]
    , goldenUEval "unitInterop" [
            getPlcNoAnn (plc (Proxy @"unitInterop") (\(d :: P.BuiltinData) -> case IsData.fromBuiltinData d of { Just t -> t P.== (); Nothing -> False}))
            , UPLC.Program () (PLC.latestVersion) (PLC.mkConstant () (IsData.toData ()))]
    , goldenUEval "mono" [plc (Proxy @"mono") (isDataRoundtrip (Mono2 2))]
    , goldenUEval "poly" [plc (Proxy @"poly") (isDataRoundtrip (Poly1 (1::Integer) (2::Integer)))]
    , goldenUEval "record" [plc (Proxy @"record") (isDataRoundtrip (MyMonoRecord 1 2))]
    , goldenUEval "list" [plc (Proxy @"list") (isDataRoundtrip ([1]::[Integer]))]
    , goldenUEval "nested" [plc (Proxy @"nested") (isDataRoundtrip (NestedRecord (Just (1, 2))))]
    , goldenUEval "bytestring" [plc (Proxy @"bytestring") (isDataRoundtrip (WrappedBS Builtins.emptyByteString))]
    , goldenPir "deconstructData" deconstructData
    , goldenPir "unsafeDeconstructData" unsafeDeconstructData
    , goldenPirReadable "matchAsData" matchAsData
    , goldenUEval "matchAsDataE" [toUPlc $ matchAsData, toUPlc $ plc (Proxy @"test") (SecondC 3)]
    , goldenPirReadable "recordAsData" recordAsData
    , goldenPirReadable "dataToData" dataToData
    , goldenPirReadable "equalityAsData" equalityAsData
    , goldenPirReadable "fieldAccessor" fieldAccessor
  ]
