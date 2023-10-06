module PlutusIR.Transform.Unwrap.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Unwrap qualified as Unwrap

test_unwrap :: TestTree
test_unwrap = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "Unwrap" $
        map
            (goldenPir Unwrap.unwrapCancel pTerm)
            -- Note: these examples don't typecheck, but we don't care
            [ "unwrapWrap"
            , "wrapUnwrap"
            ]
