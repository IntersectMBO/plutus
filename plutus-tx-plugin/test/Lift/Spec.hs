{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC   -Wno-orphans #-}
module Lift.Spec where

import           Plugin.Data.Spec
import           Plugin.Primitives.Spec

import           Common
import           PlcTestUtils

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Code
import qualified Language.PlutusTx.Lift     as Lift

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

Lift.makeLift ''MyMonoData
Lift.makeLift ''MyMonoRecord
Lift.makeLift ''MyPolyData

data NestedRecord = NestedRecord { unNested :: Maybe (Integer, Integer) }
Lift.makeLift ''NestedRecord

data WrappedBS = WrappedBS { unWrap :: Builtins.ByteString }
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
tests = testNested "Lift" [
    goldenPlc "int" (Lift.liftProgramDef (1::Integer))
    , goldenPlc "tuple" (Lift.liftProgramDef (1::Integer, 2::Integer))
    , goldenPlc "mono" (Lift.liftProgramDef (Mono2 2))
    , goldenEval "monoInterop" [ getPlc monoCase, Lift.liftProgramDef (Mono1 1 2) ]
    , goldenPlc "poly" (Lift.liftProgramDef (Poly1 (1::Integer) (2::Integer)))
    , goldenEval "polyInterop" [ getPlc defaultCasePoly, Lift.liftProgramDef (Poly1 (1::Integer) (2::Integer)) ]
    , goldenPlc "record" (Lift.liftProgramDef (MyMonoRecord 1 2))
    , goldenEval "boolInterop" [ getPlc andPlc, Lift.liftProgramDef True, Lift.liftProgramDef True ]
    , goldenPlc "list" (Lift.liftProgramDef ([1]::[Integer]))
    , goldenEval "listInterop" [ getPlc listMatch, Lift.liftProgramDef ([1]::[Integer]) ]
    , goldenPlc "nested" (Lift.liftProgramDef (NestedRecord (Just (1, 2))))
    , goldenPlc "bytestring" (Lift.liftProgramDef (WrappedBS "hello"))
    , goldenPlc "newtypeInt" (Lift.liftProgramDef (NewtypeInt 1))
    , goldenPlc "newtypeInt2" (Lift.liftProgramDef (Newtype2 $ NewtypeInt 1))
    , goldenPlc "newtypeInt3" (Lift.liftProgramDef (Newtype3 $ Newtype2 $ NewtypeInt 1))
    , goldenPlc "syn" (Lift.liftProgramDef (SynExample $ Z $ 1))
 ]
