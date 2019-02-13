{-# LANGUAGE OverloadedStrings #-}
module OptimizerSpec where

import           Common
import           TestLib

import           Language.PlutusIR.Optimizer.DeadCode
import           Language.PlutusIR.Parser
import           Language.PlutusIR.Transform.Rename   ()

optimizer :: TestNested
optimizer = testNested "optimizer" [
    deadCode
    ]

deadCode :: TestNested
deadCode = testNested "deadCode"
    $ map (goldenPir removeDeadBindings term)
    [ "typeLet"
    , "termLet"
    , "datatypeLiveType"
    , "datatypeLiveConstr"
    , "datatypeLiveDestr"
    , "datatypeDead"
    , "singleBinding"
    , "nestedBindings"
    , "nestedBindingsIndirect"
    , "recBindingSimple"
    , "recBindingComplex"
    ]
