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
test_strictifyBindings =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "StrictifyBindings"] $
    map
      (goldenPir (runIdentity . runTestPass (\tc -> strictifyBindingsPass tc def)) pTerm)
      [ "pure1"
      , "impure1"
      , "unused"
      , "conapp"
      , "strict"
      , "nonstrict1"
      , "nonstrict2"
      ]

prop_strictifyBindings :: BuiltinSemanticsVariant DefaultFun -> Property
prop_strictifyBindings biVariant =
  withMaxSuccess numTestsForPassProp
    $ testPassProp
      runIdentity
    $ \tc -> strictifyBindingsPass tc (def {_biSemanticsVariant = biVariant})
