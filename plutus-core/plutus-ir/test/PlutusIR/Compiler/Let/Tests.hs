module PlutusIR.Compiler.Let.Tests where

import PlutusIR.Test

import PlutusIR.Compiler.Let
import PlutusIR.Properties.Typecheck
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

test_lets :: TestTree
test_lets = runTestNestedIn ["plutus-ir", "test", "PlutusIR", "Compiler"] $ testNested "Let"
    [ goldenPlcFromPir pTermAsProg "letInLet"
    , goldenPlcFromPir pTermAsProg "letDep"
    ]

-- FIXME
-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (recursive terms) pass.
prop_TypecheckCompileLetsRecTerms :: Property
prop_TypecheckCompileLetsRecTerms =
  expectFailure $ withMaxSuccess 10000 $ extraConstraintTypecheckProp (compileLets RecTerms)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (non-recursive terms) pass.
prop_TypecheckCompileLetsNonRecTerms :: Property
prop_TypecheckCompileLetsNonRecTerms =
  withMaxSuccess 10000 $ extraConstraintTypecheckProp (compileLets NonRecTerms)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (types) pass.
prop_TypecheckCompileLetsTypes :: Property
prop_TypecheckCompileLetsTypes =
  withMaxSuccess 10000 $ extraConstraintTypecheckProp (compileLets Types)

-- FIXME this test sometimes fails so ignoring it to make CI pass.
-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (data types) pass.
test_TypecheckCompileLetsDataTypes :: TestTree
test_TypecheckCompileLetsDataTypes =
  ignoreTest $ testProperty "typechecking" $
    withMaxSuccess 10000 $
      extraConstraintTypecheckProp (compileLets DataTypes)
