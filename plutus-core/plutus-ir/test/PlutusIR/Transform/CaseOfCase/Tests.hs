module PlutusIR.Transform.CaseOfCase.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.CaseOfCase qualified as CaseOfCase
import PlutusPrelude
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_caseOfCase :: TestTree
test_caseOfCase =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "CaseOfCase"] $
    map
      ( goldenPir
          ( runQuote
              . runTestPass
                (\tc -> CaseOfCase.caseOfCasePassSC tc def True mempty)
          )
          pTerm
      )
      [ "basic"
      , "builtinBool"
      , "largeExpr"
      , "exponential"
      , "twoTyArgs"
      ]

prop_caseOfCase :: Property
prop_caseOfCase =
  withMaxSuccess numTestsForPassProp $
    testPassProp runQuote $
      \tc -> CaseOfCase.caseOfCasePassSC tc def True mempty
