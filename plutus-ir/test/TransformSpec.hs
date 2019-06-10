{-# LANGUAGE OverloadedStrings #-}
module TransformSpec where

import           Common
import           TestLib

import           Language.PlutusCore.Quote

import           Language.PlutusIR.Parser
import qualified Language.PlutusIR.Transform.NonStrict as NonStrict
import qualified Language.PlutusIR.Transform.ThunkRecursions as ThunkRec

transform :: TestNested
transform = testNested "transform" [
    thunkRecursions
    , nonStrict
    ]

thunkRecursions :: TestNested
thunkRecursions = testNested "thunkRecursions"
    $ map (goldenPir ThunkRec.thunkRecursions term)
    [ "listFold"
    , "monoMap"
    ]

nonStrict :: TestNested
nonStrict = testNested "nonStrict"
    $ map (goldenPir (runQuote . NonStrict.compileNonStrictBindings) term)
    [ "nonStrict1"
    ]
