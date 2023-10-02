module PlutusIR.Transform.ThunkRecursions.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Rename ()
import PlutusIR.Transform.ThunkRecursions qualified as ThunkRec
import PlutusPrelude

test_thunkRecursions :: TestTree
test_thunkRecursions = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "ThunkRecursions" $
        map
            (goldenPir (ThunkRec.thunkRecursions def) pTerm)
            [ "listFold"
            , "listFoldTrace"
            , "monoMap"
            , "errorBinding"
            , "mutuallyRecursiveValues"
            , "preserveEffectOrder"
            , "preserveStrictness"
            ]
