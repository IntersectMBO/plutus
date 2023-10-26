module PlutusIR.Transform.CaseReduce.Tests where

import PlutusIR.Transform.CaseReduce

import PlutusCore.Default
import PlutusIR.Properties.Evaluation
import PlutusIR.Properties.Typecheck
import Test.QuickCheck.Property (Property, withMaxSuccess)

-- | Check that a term typechecks after a `PlutusIR.Transform.CaseReduce.caseReduce` pass.
prop_TypecheckCaseReduce :: Property
prop_TypecheckCaseReduce =
      withMaxSuccess 3000 (pureTypecheckProp caseReduce)

-- FIXME test currently failing with an error from `lowerTerm`. The term generator should only be
-- generating builtin types but it's currently generating let terms.
-- | Check that the `caseReduce` pass preserves evaluation behaviour.
prop_Evaluation :: BuiltinSemanticsVariant DefaultFun -> Property
prop_Evaluation _biVariant =
  withMaxSuccess 50000 $ pureEvaluationProp caseReduce
