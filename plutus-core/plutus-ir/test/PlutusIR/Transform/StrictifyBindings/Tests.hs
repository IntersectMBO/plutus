module PlutusIR.Transform.StrictifyBindings.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.StrictifyBindings qualified as StrictifyBindings
import PlutusPrelude

test_strictifyBindings :: TestTree
test_strictifyBindings = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "StrictifyBindings" $
        map
            (goldenPir (StrictifyBindings.strictifyBindings def) pTerm)
            [ "pure1"
            , "impure1"
            , "unused"
            , "conapp"
            ]
