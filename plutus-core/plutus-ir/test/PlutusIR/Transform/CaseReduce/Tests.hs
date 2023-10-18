module PlutusIR.Transform.CaseReduce.Tests where

import PlutusIR.Transform.CaseReduce

import PlutusIR.Properties.Typecheck
import Test.QuickCheck.Property (Property, withMaxSuccess)

-- | Check that a term typechecks after a `PlutusIR.Transform.CaseReduce.caseReduce` pass.
prop_TypecheckCaseReduce :: Property
prop_TypecheckCaseReduce =
      withMaxSuccess 3000 (pureTypecheckProp caseReduce)
