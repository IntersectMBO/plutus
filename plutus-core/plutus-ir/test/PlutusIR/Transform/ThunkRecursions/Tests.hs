module PlutusIR.Transform.ThunkRecursions.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Builtin
import PlutusCore.Default
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Properties.Typecheck
import PlutusIR.Test
import PlutusIR.Transform.Rename ()
import PlutusIR.Transform.ThunkRecursions (thunkRecursions)
import PlutusPrelude
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_thunkRecursions :: TestTree
test_thunkRecursions = runTestNestedIn ["plutus-ir", "test", "PlutusIR", "Transform"] $
    testNested "ThunkRecursions" $
        map
            (goldenPir (thunkRecursions def) pTerm)
            [ "listFold"
            , "listFoldTrace"
            , "monoMap"
            , "errorBinding"
            , "mutuallyRecursiveValues"
            , "preserveEffectOrder"
            , "preserveStrictness"
            ]

-- | Check that a term typechecks after a `PlutusIR.Transform.ThunkRecursions.thunkRecursions` pass.
prop_TypecheckThunkRecursions :: BuiltinSemanticsVariant DefaultFun -> Property
prop_TypecheckThunkRecursions biVariant =
  withMaxSuccess 5000 $ pureTypecheckProp $
    thunkRecursions $ BuiltinsInfo biVariant defaultUniMatcherLike
