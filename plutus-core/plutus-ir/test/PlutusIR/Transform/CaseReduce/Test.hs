module PlutusIR.Transform.CaseReduce.Test where

import PlutusIR.Transform.CaseReduce

import PlutusIR.Properties.Typecheck
import Test.QuickCheck.Property (withMaxSuccess)
import Test.Tasty (TestTree)
import Test.Tasty.QuickCheck (testProperty)

test_typecheck :: TestTree
test_typecheck = testProperty "typechecking" $
      withMaxSuccess 3000 (pure_typecheck_prop caseReduce)
