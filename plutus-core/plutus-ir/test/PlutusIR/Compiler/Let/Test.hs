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
prop_typecheck_compileLets_RecTerms :: Property
prop_typecheck_compileLets_RecTerms =
  extra_constraint_typecheck_prop (compileLets RecTerms)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (non-recursive terms) pass.
prop_typecheck_compileLets_NonRecTerms :: Property
prop_typecheck_compileLets_NonRecTerms =
  extra_constraint_typecheck_prop (compileLets NonRecTerms)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (types) pass.
prop_typecheck_compileLets_Types :: Property
prop_typecheck_compileLets_Types =
  extra_constraint_typecheck_prop (compileLets Types)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (data types) pass.
prop_typecheck_compileLets_DataTypes :: Property
prop_typecheck_compileLets_DataTypes =
  extra_constraint_typecheck_prop (compileLets DataTypes)

test_typecheck :: TestTree
test_typecheck = testGroup "typechecking"
  [ -- FIXME
    expectFail $ testProperty "compileLets pass (recursive terms)" $
      withMaxSuccess 3000 prop_typecheck_compileLets_RecTerms

  , testProperty "compileLets pass (non-recursive terms)" $
      withMaxSuccess 3000 prop_typecheck_compileLets_NonRecTerms

  , testProperty "compileLets pass (types)" $
      withMaxSuccess 3000 prop_typecheck_compileLets_Types

  -- FIXME
  , expectFail $ testProperty "compileLets pass (data types)" $
      withMaxSuccess 3000 prop_typecheck_compileLets_DataTypes
  ]
