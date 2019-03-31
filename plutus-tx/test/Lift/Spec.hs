{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC   -Wno-orphans #-}
module Lift.Spec where

import           Plugin.Spec

import           Common
import           PlcTestUtils

import qualified Language.PlutusTx.Builtins as Builtins
import qualified Language.PlutusTx.Lift     as Lift
import           Language.PlutusTx.Plugin

Lift.makeLift ''MyMonoData
Lift.makeLift ''MyMonoRecord
Lift.makeLift ''MyPolyData

newtype NestedRecord = NestedRecord { unNested :: Maybe (Int, Int) }
Lift.makeLift ''NestedRecord

newtype WrappedBS = WrappedBS { unWrap :: Builtins.SizedByteString 64 }
Lift.makeLift ''WrappedBS

tests :: TestNested
tests = testNested "Lift" [
    goldenPlc "int" (Lift.unsafeLiftProgram (1::Int))
    , goldenPlc "tuple" (Lift.unsafeLiftProgram (1::Int, 2::Int))
    , goldenPlc "mono" (Lift.unsafeLiftProgram (Mono2 2))
    , goldenEval "monoInterop" [ getPlc monoCase, Lift.unsafeLiftProgram (Mono1 1 2) ]
    , goldenPlc "poly" (Lift.unsafeLiftProgram (Poly1 (1::Int) (2::Int)))
    , goldenEval "polyInterop" [ getPlc defaultCasePoly, Lift.unsafeLiftProgram (Poly1 (1::Int) (2::Int)) ]
    , goldenPlc "record" (Lift.unsafeLiftProgram (MyMonoRecord 1 2))
    , goldenEval "boolInterop" [ getPlc andPlc, Lift.unsafeLiftProgram True, Lift.unsafeLiftProgram True ]
    , goldenPlc "list" (Lift.unsafeLiftProgram ([1]::[Int]))
    , goldenEval "listInterop" [ getPlc listMatch, Lift.unsafeLiftProgram ([1]::[Int]) ]
    , goldenPlc "nested" (Lift.unsafeLiftProgram (NestedRecord (Just (1, 2))))
    , goldenPlc "bytestring" (Lift.unsafeLiftProgram (WrappedBS "hello"))
 ]
