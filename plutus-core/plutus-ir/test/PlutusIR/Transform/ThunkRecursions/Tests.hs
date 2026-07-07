module PlutusIR.Transform.ThunkRecursions.Tests where

import Test.Tasty
import Test.Tasty.Extras

import Data.Functor.Identity
import PlutusCore.Builtin
import PlutusCore.Default
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.Rename ()
import PlutusIR.Transform.ThunkRecursions
import PlutusPrelude
import Test.Cardano.Base.QuickCheck qualified as BaseQC
import Test.QuickCheck.Property (Property)

test_thunkRecursions :: TestTree
test_thunkRecursions =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "ThunkRecursions"] $
    map
      (goldenPir (runIdentity . runTestPass (\tc -> thunkRecursionsPass tc def)) pTerm)
      [ "listFold"
      , "listFoldTrace"
      , "monoMap"
      , "errorBinding"
      , "mutuallyRecursiveValues"
      , "preserveEffectOrder"
      , "preserveStrictness"
      ]

prop_thunkRecursions :: BuiltinSemanticsVariant DefaultFun -> Property
prop_thunkRecursions biVariant =
  BaseQC.withNumTests numTestsForPassProp $
    testPassProp runIdentity $
      \tc -> thunkRecursionsPass tc (def {_biSemanticsVariant = biVariant})
