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
    , "strictLet"
    , "nonstrictLet"
    , "datatypeLiveType"
    , "datatypeLiveConstr"
    , "datatypeLiveDestr"
    , "datatypeDead"
    , "singleBinding"
    , "etaBuiltinBinding"
    , "nestedBindings"
    , "nestedBindingsIndirect"
    , "recBindingSimple"
    , "recBindingComplex"
    ]

{- There used to be a test checking that zero-argument builtin
   applications were *not* eliminated, but that became irrelevant once
   we required builtins to be saturated and non-nullary.  Remember to
   add a suitable test if we ever allow nullary builtins. -}
