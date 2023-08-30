-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC   -Wno-orphans #-}
module Lift.Spec where

import Test.Tasty.Extras

import Plugin.Data.Spec
import Plugin.Primitives.Spec

import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Lift qualified as Lift
import PlutusTx.Test ()

Lift.makeLift ''MyMonoData
Lift.makeLift ''MyMonoRecord
Lift.makeLift ''MyPolyData

data NestedRecord = NestedRecord { unNested :: Maybe (Integer, Integer) }
Lift.makeLift ''NestedRecord

data WrappedBS = WrappedBS { unWrap :: Builtins.BuiltinByteString }
Lift.makeLift ''WrappedBS

newtype NewtypeInt = NewtypeInt { unNt :: Integer }
Lift.makeLift ''NewtypeInt

newtype Newtype2 = Newtype2 { unNt2 :: NewtypeInt }
Lift.makeLift ''Newtype2

newtype Newtype3 = Newtype3 { unNt3 :: Newtype2 }
Lift.makeLift ''Newtype3

-- 'Z' so it sorts late and this doesn't work by accident
data Z = Z Integer
Lift.makeLift ''Z
type Syn = Z

data SynExample = SynExample { unSE :: Syn }
Lift.makeLift ''SynExample

tests :: TestNested
tests = testNestedGhc "Lift" [
    goldenUPlc "int" (snd (Lift.liftProgramDef (1::Integer)))
    , goldenUPlc "tuple" (snd (Lift.liftProgramDef (1::Integer, 2::Integer)))
    , goldenUPlc "mono" (snd (Lift.liftProgramDef (Mono2 2)))
    , goldenUEval "monoInterop" [ getPlcNoAnn monoCase, snd (Lift.liftProgramDef (Mono1 1 2)) ]
    , goldenUPlc "poly" (snd (Lift.liftProgramDef (Poly1 (1::Integer) (2::Integer))))
    , goldenUEval "polyInterop" [ getPlcNoAnn defaultCasePoly, snd (Lift.liftProgramDef (Poly1 (1::Integer) (2::Integer))) ]
    , goldenUPlc "record" (snd (Lift.liftProgramDef (MyMonoRecord 1 2)))
    , goldenUEval "boolInterop" [ getPlcNoAnn andPlc, snd (Lift.liftProgramDef True), snd (Lift.liftProgramDef True) ]
    , goldenUPlc "list" (snd (Lift.liftProgramDef ([1]::[Integer])))
    , goldenUEval "listInterop" [ getPlcNoAnn listMatch, snd (Lift.liftProgramDef ([1]::[Integer])) ]
    , goldenUPlc "nested" (snd (Lift.liftProgramDef (NestedRecord (Just (1, 2)))))
    , goldenUPlc "bytestring" (snd (Lift.liftProgramDef (WrappedBS "hello")))
    , goldenUPlc "newtypeInt" (snd (Lift.liftProgramDef (NewtypeInt 1)))
    , goldenUPlc "newtypeInt2" (snd (Lift.liftProgramDef (Newtype2 $ NewtypeInt 1)))
    , goldenUPlc "newtypeInt3" (snd (Lift.liftProgramDef (Newtype3 $ Newtype2 $ NewtypeInt 1)))
    , goldenUPlc "syn" (snd (Lift.liftProgramDef (SynExample $ Z $ 1)))
 ]
