{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module OptimizerSpec where

import           Common
import           TestLib

import           Language.PlutusIR.Optimizer.DeadCode
import           Language.PlutusIR.Parser
import           Language.PlutusIR.Transform.Rename   ()

import qualified Language.PlutusCore                  as PLC
import qualified Language.PlutusCore.Constant.Dynamic as PLC

optimizer :: TestNested
optimizer = testNested "optimizer" [
    deadCode
    ]

deadCode :: TestNested
deadCode =
    let means = PLC.getStringBuiltinMeanings @(PLC.Term PLC.TyName PLC.Name PLC.DefaultUni () ())
    in testNested "deadCode"
    $ map (goldenPir (removeDeadBindings means) term)
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
