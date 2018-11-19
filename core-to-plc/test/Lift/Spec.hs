{-# OPTIONS_GHC   -Wno-orphans #-}
module Lift.Spec where

import           Plugin.IllTyped
import           Plugin.Spec

import           Common
import           PlcTestUtils

import           Language.Plutus.CoreToPLC.Plugin
import           Language.Plutus.Lift

import           Language.PlutusCore

instance LiftPlc MyMonoData
instance LiftPlc MyMonoRecord

tests :: TestNested
tests = testNested "Lift" [
    goldenPlc "int" (trivialProgram $ runQuote $ lift (1::Int))
    , goldenPlc "mono" (trivialProgram $ runQuote $ lift (Mono2 2))
    , goldenEval "monoInterop" [ getAst monoCase, trivialProgram $ runQuote $ lift (Mono1 1 2) ]
    , goldenPlc "record" (trivialProgram $ runQuote $ lift (MyMonoRecord 1 2))
    , goldenEval "boolInterop" [ getAst andPlc, trivialProgram $ runQuote $ lift True, trivialProgram $ runQuote $ lift True ]
    , goldenPlc "list" (trivialProgram $ runQuote $ lift ([1]::[Int]))
    , goldenEval "listInterop" [ getAst listMatch, trivialProgram $ runQuote $ lift ([1]::[Int]) ]
    , goldenPlc "liftPlc" (trivialProgram $ runQuote $ lift int)
  ]
