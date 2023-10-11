module PlutusIR.Transform.StrictifyBindings.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Default.Builtins
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Properties.Typecheck (pureTypecheckProp)
import PlutusIR.Test
import PlutusIR.Transform.StrictifyBindings
import PlutusPrelude
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_strictifyBindings :: TestTree
test_strictifyBindings = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "StrictifyBindings" $
        map
            (goldenPir (strictifyBindings def) pTerm)
            [ "pure1"
            , "impure1"
            , "unused"
            , "conapp"
            ]

-- | Check that a term typechecks after a
-- `PlutusIR.Transform.StrictifyBindings` pass.
prop_TypecheckStrictifyBindings :: BuiltinSemanticsVariant DefaultFun -> Property
prop_TypecheckStrictifyBindings biVariant =
  withMaxSuccess 5000 $ pureTypecheckProp (strictifyBindings (BuiltinsInfo biVariant))
