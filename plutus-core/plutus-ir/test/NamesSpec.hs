module NamesSpec
    ( names
    ) where


import PlutusCore.Rename
import PlutusCore.Test

import PlutusIR.Generators.AST
import PlutusIR.Mark
import PlutusIR.Transform.Rename

import Test.Tasty

names :: TestTree
names =
    testGroup "names"
        [ test_scopingGood genProgram rename
        , test_scopingBad genProgram markNonFreshProgram renameProgramM
        ]
