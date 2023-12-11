module PlutusIR.Transform.StrictifyBindings.Tests where

import Test.Tasty
import Test.Tasty.Extras

import Data.Functor.Identity
import PlutusCore.Default.Builtins
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.StrictifyBindings
import PlutusPrelude
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_strictifyBindings :: TestTree
test_strictifyBindings = runTestNestedIn ["plutus-ir", "test", "PlutusIR", "Transform"] $
    testNested "StrictifyBindings" $
        map
            (goldenPir (runIdentity . runTestPass (\tc -> strictifyBindingsPass tc def)) pTerm)
            [ "pure1"
            , "impure1"
            , "unused"
            , "conapp"
            ]

prop_strictifyBindings :: BuiltinSemanticsVariant DefaultFun -> Property
prop_strictifyBindings biVariant =
  withMaxSuccess numTestsForPassProp $
    testPassProp
      runIdentity
      $ \tc -> strictifyBindingsPass tc (def {_biSemanticsVariant = biVariant})
