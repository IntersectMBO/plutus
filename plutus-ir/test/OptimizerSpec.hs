{-# LANGUAGE OverloadedStrings #-}
module OptimizerSpec where

import           Common
import           TestLib

import           Language.PlutusIR.Optimizer.DeadCode
import           Language.PlutusIR.Optimizer.Merge
import           Language.PlutusIR.Parser
import           Language.PlutusIR.Transform.Rename   ()

optimizer :: TestNested
optimizer = testNested "optimizer" [
    deadCode
    , merge
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

merge :: TestNested
merge = testNested "merge"
    $ map (goldenPir mergeLets term)
    [ "simpleMerge"
    , "simpleMergeThree"
    , "dependent"
    , "dependent2"
    , "dependent3"
    , "dependent4"
    , "recursiveBlock"
    ]
