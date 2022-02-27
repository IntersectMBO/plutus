{-# LANGUAGE TypeApplications #-}

module NamesSpec
    ( names
    ) where


import PlutusIR.Generators.AST
import PlutusIR.Mark
import PlutusIR.Transform.Rename

import PlutusCore.Rename
import PlutusCore.Test

import Test.Tasty

names :: TestTree
names =
    testGroup "names"
        [ test_scopingGood genProgram rename
        , test_scopingBad genProgram markNonFreshProgram renameProgramM
        ]
