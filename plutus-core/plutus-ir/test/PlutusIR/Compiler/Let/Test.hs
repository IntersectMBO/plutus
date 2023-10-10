module PlutusIR.Compiler.Let.Test where

import PlutusIR.Test

import PlutusIR.Compiler.Let
import PlutusIR.Properties.Typecheck
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

test_lets :: TestTree
test_lets = runTestNestedIn ["plutus-ir/test/PlutusIR/Compiler"] $ testNested "Let"
    [ goldenPlcFromPir pTermAsProg "letInLet"
    , goldenPlcFromPir pTermAsProg "letDep"
    ]

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (recursive terms) pass.
typecheckCompileLetsRecTermsProp :: Property
typecheckCompileLetsRecTermsProp =
  extraConstraintTypecheckProp (compileLets RecTerms)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (non-recursive terms) pass.
typecheckCompileLetsNonRecTermsProp :: Property
typecheckCompileLetsNonRecTermsProp =
  extraConstraintTypecheckProp (compileLets NonRecTerms)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (types) pass.
typecheckCompileLetsTypesProp :: Property
typecheckCompileLetsTypesProp =
  extraConstraintTypecheckProp (compileLets Types)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (data types) pass.
typecheckCompileLetsDataTypesProp :: Property
typecheckCompileLetsDataTypesProp =
  extraConstraintTypecheckProp (compileLets DataTypes)

test_typecheck :: TestTree
test_typecheck = testGroup "typechecking"
  [ -- FIXME
    expectFail $ testProperty "compileLets pass (recursive terms)" $
      withMaxSuccess 3000 typecheckCompileLetsRecTermsProp

  , testProperty "compileLets pass (non-recursive terms)" $
      withMaxSuccess 3000 typecheckCompileLetsNonRecTermsProp

  , testProperty "compileLets pass (types)" $
      withMaxSuccess 3000 typecheckCompileLetsTypesProp

  -- FIXME
  , expectFail $ testProperty "compileLets pass (data types)" $
      withMaxSuccess 10000 typecheckCompileLetsDataTypesProp
  ]
