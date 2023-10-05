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
typecheck_compileLets_RecTerms_prop :: Property
typecheck_compileLets_RecTerms_prop =
  extra_constraint_typecheck_prop (compileLets RecTerms)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (non-recursive terms) pass.
typecheck_compileLets_NonRecTerms_prop :: Property
typecheck_compileLets_NonRecTerms_prop =
  extra_constraint_typecheck_prop (compileLets NonRecTerms)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (types) pass.
typecheck_compileLets_Types_prop :: Property
typecheck_compileLets_Types_prop =
  extra_constraint_typecheck_prop (compileLets Types)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (data types) pass.
typecheck_compileLets_DataTypes_prop :: Property
typecheck_compileLets_DataTypes_prop =
  extra_constraint_typecheck_prop (compileLets DataTypes)

test_typecheck :: TestTree
test_typecheck = testGroup "typechecking"
  [ -- FIXME
    expectFail $ testProperty "compileLets pass (recursive terms)" $
      withMaxSuccess 3000 typecheck_compileLets_RecTerms_prop

  , testProperty "compileLets pass (non-recursive terms)" $
      withMaxSuccess 3000 typecheck_compileLets_NonRecTerms_prop

  , testProperty "compileLets pass (types)" $
      withMaxSuccess 3000 typecheck_compileLets_Types_prop

  -- FIXME
  , expectFail $ testProperty "compileLets pass (data types)" $
      withMaxSuccess 3000 typecheck_compileLets_DataTypes_prop
  ]
