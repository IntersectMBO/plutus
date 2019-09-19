{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
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
    goldenPlc "int" (Lift.liftProgram (1::Integer))
    , goldenPlc "tuple" (Lift.liftProgram (1::Integer, 2::Integer))
    , goldenPlc "mono" (Lift.liftProgram (Mono2 2))
    , goldenEval "monoInterop" [ getPlc monoCase, Lift.liftProgram (Mono1 1 2) ]
    , goldenPlc "poly" (Lift.liftProgram (Poly1 (1::Integer) (2::Integer)))
    , goldenEval "polyInterop" [ getPlc defaultCasePoly, Lift.liftProgram (Poly1 (1::Integer) (2::Integer)) ]
    , goldenPlc "record" (Lift.liftProgram (MyMonoRecord 1 2))
    , goldenEval "boolInterop" [ getPlc andPlc, Lift.liftProgram True, Lift.liftProgram True ]
    , goldenPlc "list" (Lift.liftProgram ([1]::[Integer]))
    , goldenEval "listInterop" [ getPlc listMatch, Lift.liftProgram ([1]::[Integer]) ]
    , goldenPlc "nested" (Lift.liftProgram (NestedRecord (Just (1, 2))))
    , goldenPlc "bytestring" (Lift.liftProgram (WrappedBS "hello"))
    , goldenPlc "newtypeInt" (Lift.liftProgram (NewtypeInt 1))
    , goldenPlc "newtypeInt2" (Lift.liftProgram (Newtype2 $ NewtypeInt 1))
    , goldenPlc "newtypeInt3" (Lift.liftProgram (Newtype3 $ Newtype2 $ NewtypeInt 1))
    , goldenPlc "syn" (Lift.liftProgram (SynExample $ Z $ 1))
 ]
