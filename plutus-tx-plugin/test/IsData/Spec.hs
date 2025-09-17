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
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module IsData.Spec where

import Test.Tasty.Extras

import Plugin.Data.Spec

import PlutusCore.Test
import PlutusTx.AsData qualified as AsData
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Code
import PlutusTx.IsData qualified as IsData
import PlutusTx.Plugin
import PlutusTx.Prelude qualified as P
import PlutusTx.Test

import Data.Proxy

data MyMonoRecordAsList = MyMonoRecordAsList {mrlA :: Integer, mrlB :: Integer}
instance P.Eq MyMonoRecordAsList where
  {-# INLINEABLE (==) #-}
  (MyMonoRecordAsList x1 y1) == (MyMonoRecordAsList x2 y2) = x1 P.== x2 && y1 P.== y2
IsData.makeIsDataAsList ''MyMonoRecordAsList

IsData.unstableMakeIsData ''MyMonoData
IsData.unstableMakeIsData ''MyMonoRecord
IsData.unstableMakeIsData ''MyPolyData

data NestedRecord = NestedRecord {unNested :: Maybe (Integer, Integer)}
IsData.unstableMakeIsData ''NestedRecord

instance P.Eq NestedRecord where
  {-# INLINEABLE (==) #-}
  (NestedRecord i1) == (NestedRecord i2) = i1 P.== i2

data WrappedBS = WrappedBS {unWrap :: Builtins.BuiltinByteString}
IsData.unstableMakeIsData ''WrappedBS

instance P.Eq WrappedBS where
  {-# INLINEABLE (==) #-}
  (WrappedBS i1) == (WrappedBS i2) = i1 P.== i2

deconstructData :: CompiledCode (Builtins.BuiltinData -> Maybe (Integer, Integer))
deconstructData = plc (Proxy @"deconstructData4") (\(d :: Builtins.BuiltinData) -> IsData.fromBuiltinData d)

unsafeDeconstructData :: CompiledCode (Builtins.BuiltinData -> Maybe (Integer, Integer))
unsafeDeconstructData = plc (Proxy @"deconstructData4") (\(d :: Builtins.BuiltinData) -> IsData.unsafeFromBuiltinData d)

isDataRoundtrip
  :: (IsData.FromData a, IsData.UnsafeFromData a, IsData.ToData a, P.Eq a) => a -> Bool
isDataRoundtrip a =
  let d = IsData.toBuiltinData a
      safeRoundtrip = case IsData.fromBuiltinData d of
        Just a' -> a P.== a'
        Nothing -> False
      unsafeRoundtrip = IsData.unsafeFromBuiltinData d P.== a
   in safeRoundtrip && unsafeRoundtrip
{-# INLINEABLE isDataRoundtrip #-}

AsData.asData
  [d|
    data SecretlyData = FirstC () | SecondC Integer
      deriving newtype (P.Eq, IsData.FromData, IsData.UnsafeFromData, IsData.ToData)
    |]

AsData.asData
  [d|
    data RecordConstructor a = RecordConstructor {x :: a, y :: Integer}
    |]

AsData.asData
  [d|
    data MaybeD a = JustD a | NothingD
      deriving newtype (P.Eq, IsData.FromData, IsData.UnsafeFromData, IsData.ToData)
    |]

-- Features a nested field which is also defined with AsData
matchAsData :: CompiledCode (MaybeD SecretlyData -> SecretlyData)
matchAsData =
  plc
    (Proxy @"matchAsData")
    ( \case
        JustD a -> a
        NothingD -> FirstC ()
    )

recordAsData :: CompiledCode (RecordConstructor Integer)
recordAsData = plc (Proxy @"recordAsData") (RecordConstructor 1 2)

dataToData :: CompiledCode (RecordConstructor Integer -> SecretlyData)
dataToData =
  plc
    (Proxy @"dataToData")
    ( \case
        RecordConstructor a b | a P.== 3, b P.== 4 -> SecondC (Builtins.addInteger a b)
        _ -> FirstC ()
    )

-- Should ultimately use equalsData
equalityAsData :: CompiledCode (SecretlyData -> SecretlyData -> Bool)
equalityAsData = plc (Proxy @"equalityAsData") (\x y -> x P.== y)

fieldAccessor :: CompiledCode (RecordConstructor Integer -> Integer)
fieldAccessor = plc (Proxy @"fieldAccessor") (\r -> x r)

tests :: TestNested
tests =
  testNested "IsData" . pure $
    testNestedGhc
      [ assertResult "int" (plc (Proxy @"int") (isDataRoundtrip (1 :: Integer)))
      , assertResult "tuple" (plc (Proxy @"tuple") (isDataRoundtrip (1 :: Integer, 2 :: Integer)))
      , assertResult
          "tupleInterop"
          ( unsafeApplyCodeN
              ( plc (Proxy @"tupleInterop")
                  ( \(d :: P.BuiltinData) ->
                      case IsData.fromBuiltinData d of
                        Just t  -> t P.== (1 :: Integer, 2 :: Integer)
                        Nothing -> False
                  )
              )
              (plc (Proxy @"tupleInteropArg") (P.toBuiltinData (1 :: Integer, 2 :: Integer)))
          )
      , assertResult
          "unsafeTupleInterop"
          ( unsafeApplyCodeN
              ( plc (Proxy @"unsafeTupleInterop")
                  (\(d :: P.BuiltinData) ->
                     IsData.unsafeFromBuiltinData d P.== (1 :: Integer, 2 :: Integer)
                  )
              )
              (plc (Proxy @"unsafeTupleInteropArg") (P.toBuiltinData (1 :: Integer, 2 :: Integer)))
          )
      , assertResult "unit" (plc (Proxy @"unit") (isDataRoundtrip ()))
      , assertResult
          "unitInterop"
          ( unsafeApplyCodeN
              ( plc (Proxy @"unitInterop")
                  (\(d :: P.BuiltinData) ->
                     case IsData.fromBuiltinData d of
                       Just t  -> t P.== ()
                       Nothing -> False
                  )
              )
              (plc (Proxy @"unitInteropArg") (P.toBuiltinData ()))
          )
      , assertResult "mono" (plc (Proxy @"mono") (isDataRoundtrip (Mono2 2)))
      , assertResult "poly" (plc (Proxy @"poly") (isDataRoundtrip (Poly1 (1 :: Integer) (2 :: Integer))))
      , assertResult "record" (plc (Proxy @"record") (isDataRoundtrip (MyMonoRecord 1 2)))
      , assertResult "recordAsList" (plc (Proxy @"record") (isDataRoundtrip (MyMonoRecordAsList 1 2)))
      , assertResult "recordAsList is List"
          (plc (Proxy @"record") (
              P.toBuiltinData (MyMonoRecordAsList 1 2)
              P.== (BI.mkList $
                      BI.mkCons (P.toBuiltinData @Integer 1) $
                      BI.mkCons (P.toBuiltinData @Integer 2) $
                      BI.mkNilData BI.unitval)))
      , assertResult "list" (plc (Proxy @"list") (isDataRoundtrip ([1] :: [Integer])))
      , assertResult "nested" (plc (Proxy @"nested") (isDataRoundtrip (NestedRecord (Just (1, 2)))))
      , assertResult
          "bytestring"
          (plc (Proxy @"bytestring") (isDataRoundtrip (WrappedBS Builtins.emptyByteString)))
      , goldenPirReadable "deconstructData" deconstructData
      , goldenPirReadable "unsafeDeconstructData" unsafeDeconstructData
      , goldenPirReadable "matchAsData" matchAsData
      , goldenUEval "matchAsDataE"
          [ unsafeApplyCodeN
              matchAsData
              (plc (Proxy @"test") (P.unsafeFromBuiltinData $ P.toBuiltinData $ SecondC 3))
          ]
      , goldenPirReadable "recordAsData" recordAsData
      , goldenPirReadable "dataToData" dataToData
      , goldenPirReadable "equalityAsData" equalityAsData
      , goldenPirReadable "fieldAccessor" fieldAccessor
      , goldenPirReadable "MyMonoRecordAsListToData"
          (plc (Proxy @"MyMonoRecordAsListToData") (IsData.toBuiltinData @MyMonoRecordAsList))
      , $(goldenCodeGen "MyMonoRecordAsList" (IsData.makeIsDataAsList ''MyMonoRecord))
      , $(goldenCodeGen "MyMonoRecord" (IsData.unstableMakeIsData ''MyMonoRecord))
      , $(goldenCodeGen "MyMonoData" (IsData.unstableMakeIsData ''MyMonoData))
      , $(goldenCodeGen "MyPolyData" (IsData.unstableMakeIsData ''MyPolyData))
      ]
