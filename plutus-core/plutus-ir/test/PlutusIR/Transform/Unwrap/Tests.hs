module PlutusIR.Transform.Unwrap.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Unwrap qualified as Unwrap

import PlutusIR.Properties.Typecheck
import Test.QuickCheck.Property (withMaxSuccess)
import Test.Tasty.QuickCheck (testProperty)

test_unwrap :: TestTree
test_unwrap = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "Unwrap" $
        map
            (goldenPir Unwrap.unwrapCancel pTerm)
            -- Note: these examples don't typecheck, but we don't care
            [ "unwrapWrap"
            , "wrapUnwrap"
            ]

test_typecheck :: TestTree
test_typecheck = testProperty "typechecking" $
    withMaxSuccess 3000 (pure_typecheck_prop Unwrap.unwrapCancel)
