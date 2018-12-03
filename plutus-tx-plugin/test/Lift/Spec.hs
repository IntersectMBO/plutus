{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC   -Wno-orphans #-}
module Lift.Spec where

import           Plugin.IllTyped
import           Plugin.Spec

import           Common
import           PlcTestUtils

import qualified Language.PlutusTx.Lift    as Lift
import           Language.PlutusTx.Plugin

import           Language.PlutusCore.Quote

Lift.makeLift ''MyMonoData
Lift.makeLift ''MyMonoRecord
Lift.makeLift ''MyPolyData

newtype NestedRecord = NestedRecord { unNested :: Maybe (Int, Int) }
Lift.makeLift ''NestedRecord

tests :: TestNested
tests = testNested "Lift" [
    goldenPlc "int" (Lift.unsafeLiftPlcProgram (1::Int))
    , goldenPlc "tuple" (Lift.unsafeLiftPlcProgram (1::Int, 2::Int))
    , goldenPlc "mono" (Lift.unsafeLiftPlcProgram (Mono2 2))
    , goldenEval "monoInterop" [ getAst monoCase, Lift.unsafeLiftPlcProgram (Mono1 1 2) ]
    , goldenPlc "poly" (Lift.unsafeLiftPlcProgram (Poly1 (1::Int) (2::Int)))
    , goldenEval "polyInterop" [ getAst defaultCasePoly, Lift.unsafeLiftPlcProgram (Poly1 (1::Int) (2::Int)) ]
    , goldenPlc "record" (Lift.unsafeLiftPlcProgram (MyMonoRecord 1 2))
    , goldenEval "boolInterop" [ getAst andPlc, Lift.unsafeLiftPlcProgram True, Lift.unsafeLiftPlcProgram True ]
    , goldenPlc "list" (Lift.unsafeLiftPlcProgram ([1]::[Int]))
    , goldenEval "listInterop" [ getAst listMatch, Lift.unsafeLiftPlcProgram ([1]::[Int]) ]
    , goldenPlc "nested" (Lift.unsafeLiftPlcProgram (NestedRecord (Just (1, 2))))
 ]
