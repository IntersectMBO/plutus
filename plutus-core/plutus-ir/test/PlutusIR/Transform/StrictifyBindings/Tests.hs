module PlutusIR.Transform.StrictifyBindings.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Default.Builtins
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Properties.Typecheck (pure_typecheck_prop)
import PlutusIR.Test
import PlutusIR.Transform.StrictifyBindings
import PlutusPrelude
import Test.QuickCheck.Property (Property, withMaxSuccess)
import Test.Tasty.QuickCheck (testProperty)

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
prop_typecheck_strictifyBindings :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_strictifyBindings biVariant =
  pure_typecheck_prop (strictifyBindings (BuiltinsInfo biVariant))

test_typecheck :: TestTree
test_typecheck = testGroup "typechecking"
  [ testProperty "Builtin Variant 1" $
      withMaxSuccess 3000 (prop_typecheck_strictifyBindings DefaultFunSemanticsVariant1)
  , testProperty "Builtin Variant 2" $
      withMaxSuccess 3000 (prop_typecheck_strictifyBindings DefaultFunSemanticsVariant2)
  ]
