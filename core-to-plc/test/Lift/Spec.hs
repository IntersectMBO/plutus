{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC   -Wno-orphans #-}
module Lift.Spec where

import           Plugin.IllTyped
import           Plugin.Spec

import           Common
import           PlcTestUtils

import           Language.Plutus.CoreToPLC.Plugin
import qualified Language.Plutus.Lift             as Lift

import           Language.PlutusCore.Quote

Lift.makeLift ''MyMonoData
Lift.makeLift ''MyMonoRecord
Lift.makeLift ''MyPolyData

newtype NestedRecord = NestedRecord { unNested :: Maybe (Int, Int) }
Lift.makeLift ''NestedRecord

tests :: TestNested
tests = testNested "Lift" [
    goldenPlc "int" (trivialProgram $ runQuote $ Lift.unsafeLiftPlc (1::Int))
    , goldenPlc "tuple" (trivialProgram $ runQuote $ Lift.unsafeLiftPlc (1::Int, 2::Int))
    , goldenPlc "mono" (trivialProgram $ runQuote $ Lift.unsafeLiftPlc (Mono2 2))
    , goldenEval "monoInterop" [ getAst monoCase, trivialProgram $ runQuote $ Lift.unsafeLiftPlc (Mono1 1 2) ]
    , goldenPlc "poly" (trivialProgram $ runQuote $ Lift.unsafeLiftPlc (Poly1 (1::Int) (2::Int)))
    , goldenEval "polyInterop" [ getAst defaultCasePoly, trivialProgram $ runQuote $ Lift.unsafeLiftPlc (Poly1 (1::Int) (2::Int)) ]
    , goldenPlc "record" (trivialProgram $ runQuote $ Lift.unsafeLiftPlc (MyMonoRecord 1 2))
    , goldenEval "boolInterop" [ getAst andPlc, trivialProgram $ runQuote $ Lift.unsafeLiftPlc True, trivialProgram $ runQuote $ Lift.unsafeLiftPlc True ]
    , goldenPlc "list" (trivialProgram $ runQuote $ Lift.unsafeLiftPlc ([1]::[Int]))
    , goldenEval "listInterop" [ getAst listMatch, trivialProgram $ runQuote $ Lift.unsafeLiftPlc ([1]::[Int]) ]
    , goldenPlc "nested" (trivialProgram $ runQuote $ Lift.unsafeLiftPlc (NestedRecord (Just (1, 2))))
 ]
