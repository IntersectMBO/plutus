module PlutusIR.Transform.DeadCode.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Default
import PlutusCore.Quote
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.DeadCode
import PlutusPrelude
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.QuickCheck

test_deadCode :: TestTree
test_deadCode =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "DeadCode"] $
    map
      (goldenPir (runQuote . runTestPass (\tc -> removeDeadBindingsPassSC tc def)) pTerm)
      [ "typeLet"
      , "termLet"
      , "strictLet"
      , "nonstrictLet"
      , "datatypeLiveType"
      , "datatypeLiveConstr"
      , "datatypeLiveDestr"
      , "datatypeDead"
      , "singleBinding"
      , "builtinBinding"
      , "etaBuiltinBinding"
      , "nestedBindings"
      , "nestedBindingsIndirect"
      , "recBindingSimple"
      , "recBindingComplex"
      , "pruneDatatype"
      ]

-- FIXME (https://github.com/IntersectMBO/plutus-private/issues/1877):
-- this test sometimes fails so ignoring it to make CI pass.
typecheckRemoveDeadBindingsProp :: BuiltinSemanticsVariant DefaultFun -> Property
typecheckRemoveDeadBindingsProp biVariant =
  withMaxSuccess (3 * numTestsForPassProp)
    $ testPassProp
      runQuote
    $ \tc -> removeDeadBindingsPassSC tc (def {_biSemanticsVariant = biVariant})
test_deadCodeP :: TestTree
test_deadCodeP =
  ignoreTest $ testProperty "deadCode" typecheckRemoveDeadBindingsProp
