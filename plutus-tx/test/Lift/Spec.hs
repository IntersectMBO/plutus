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

tests :: TestNested
tests = testNested "Lift" [
    goldenPlc "int" (Lift.unsafeLiftProgram (1::Integer))
    , goldenPlc "tuple" (Lift.unsafeLiftProgram (1::Integer, 2::Integer))
    , goldenPlc "mono" (Lift.unsafeLiftProgram (Mono2 2))
    , goldenEval "monoInterop" [ getPlc monoCase, Lift.unsafeLiftProgram (Mono1 1 2) ]
    , goldenPlc "poly" (Lift.unsafeLiftProgram (Poly1 (1::Integer) (2::Integer)))
    , goldenEval "polyInterop" [ getPlc defaultCasePoly, Lift.unsafeLiftProgram (Poly1 (1::Integer) (2::Integer)) ]
    , goldenPlc "record" (Lift.unsafeLiftProgram (MyMonoRecord 1 2))
    , goldenEval "boolInterop" [ getPlc andPlc, Lift.unsafeLiftProgram True, Lift.unsafeLiftProgram True ]
    , goldenPlc "list" (Lift.unsafeLiftProgram ([1]::[Integer]))
    , goldenEval "listInterop" [ getPlc listMatch, Lift.unsafeLiftProgram ([1]::[Integer]) ]
    , goldenPlc "nested" (Lift.unsafeLiftProgram (NestedRecord (Just (1, 2))))
    , goldenPlc "bytestring" (Lift.unsafeLiftProgram (WrappedBS "hello"))
    , goldenPlc "newtypeInt" (Lift.unsafeLiftProgram (NewtypeInt 1))
    , goldenPlc "newtypeInt2" (Lift.unsafeLiftProgram (Newtype2 $ NewtypeInt 1))
    , goldenPlc "newtypeInt3" (Lift.unsafeLiftProgram (Newtype3 $ Newtype2 $ NewtypeInt 1))
 ]
