module PlutusIR.Transform.Unwrap.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Unwrap

import PlutusIR.Properties.Typecheck
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_unwrap :: TestTree
test_unwrap = runTestNestedIn ["plutus-ir", "test", "PlutusIR", "Transform"] $
    testNested "Unwrap" $
        map
            (goldenPir unwrapCancel pTerm)
            -- Note: these examples don't typecheck, but we don't care
            [ "unwrapWrap"
            , "wrapUnwrap"
            ]

-- | Check that a term typechecks after a `PlutusIR.Transform.Unwrap.unwrapCancel` pass.
prop_TypecheckUnwrap :: Property
prop_TypecheckUnwrap =
    withMaxSuccess 3000 (pureTypecheckProp unwrapCancel)
