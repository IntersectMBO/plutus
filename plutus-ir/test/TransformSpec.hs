{-# LANGUAGE OverloadedStrings #-}
module TransformSpec where

import           Common
import           TestLib

import           Language.PlutusCore.Quote

import           Language.PlutusIR.Parser
import           Language.PlutusIR.Transform.ThunkRecursions

transform :: TestNested
transform = testNested "transform" [
    thunkRecursions
    ]

thunkRecursions :: TestNested
thunkRecursions = testNested "thunkRecursions"
    $ map (goldenPir (runQuote . thunkRecursionsTerm) term)
    [ "listFold"
    , "monoMap"
    ]
