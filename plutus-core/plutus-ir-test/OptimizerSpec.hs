{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module OptimizerSpec where

import           Common
import           TestLib

import           Language.PlutusIR.Optimizer.DeadCode
import           Language.PlutusIR.Parser
import           Language.PlutusIR.Transform.Rename   ()

import qualified Language.PlutusCore                  as PLC

optimizer :: TestNested
optimizer = testNested "optimizer" [
    deadCode
    ]

deadCode :: TestNested
deadCode =
    testNested "deadCode"
    $ map (goldenPir removeDeadBindings $ term @PLC.DefaultUni @PLC.DefaultFun)
    [ "typeLet"
    , "termLet"
    , "strictLet"
    , "nonstrictLet"
    , "datatypeLiveType"
    , "datatypeLiveConstr"
    , "datatypeLiveDestr"
    , "datatypeDead"
    , "singleBinding"
    , "builtinBinding"
    , "etaBuiltinBinding"
    , "nestedBindings"
    , "nestedBindingsIndirect"
    , "recBindingSimple"
    , "recBindingComplex"
    ]
