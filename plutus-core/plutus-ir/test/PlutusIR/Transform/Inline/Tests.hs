module PlutusIR.Transform.Inline.Tests where

import Test.Tasty.Extras

import PlutusCore.Default.Builtins
import PlutusCore.Quote
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.Inline.Inline
import PlutusPrelude
import Test.QuickCheck.Property (Property, withMaxSuccess)
import Test.Tasty (TestTree)

-- | Tests of the inliner, include global uniqueness test.
test_inline :: TestTree
test_inline =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "Inline"] $
    map
      (runTest withConstantInlining)
      [ "var"
      , "builtin"
      , "callsite-6970"
      , "callsite-non-trivial-body"
      , "constant"
      , "transitive"
      , "tyvar"
      , "single"
      , "immediateVar"
      , "immediateApp"
      , "firstEffectfulTerm1"
      , "firstEffectfulTerm2"
      , -- these tests are all let bindings of functions
        "letFunConstInt" -- const fn fully applied (integer)
      , "letFunConstBool" -- const fn fully applied (bool)
      , "letFunConstMulti" -- multiple occurrences of a let binding of the const fn.
      , "letFunInFun" -- fully applied fn inside another let, single occurrence.
      , "letFunInFunMulti" -- fully applied fn inside another let, multiple occurrences.
      -- similar to "letFunInFunMulti" but all fns are fully applied.
      , "letTypeAppMulti"
      , -- singe occurrence of a polymorphic id function that is fully applied
        "letTypeApp"
      , "letTypeApp2" -- multiple occurrences of a function with type application
      -- multiple occurrences of a polymorphic id function that IS fully applied
      , "letTypeAppMultiSat"
      , -- multiple occurrences of a polymorphic id function that is NOT fully applied
        "letTypeAppMultiNotSat"
      , "letApp" -- single occurrence of a function application in rhs
      -- multiple occurrences of a function application in rhs with not acceptable body
      , "letAppMultiNotAcceptable"
      , "letOverApp" -- over-application of a function, single occurrence
      , "letOverAppMulti" -- multiple occurrences of an over-application of a function
      -- multiple occurrences of an over-application of a function with type arguments
      , "letOverAppType"
      , "letNonPure" -- multiple occurrences of a non-pure binding
      , "letNonPureMulti"
      , "letNonPureMultiStrict"
      , "multilet"
      , "rhs-modified"
      , "partiallyApp"
      , "effectfulBuiltinArg"
      , "nameCapture"
      , "inlineConstantsOn"
      ]
      <> [runTest withoutConstantInlining "inlineConstantsOff"]
  where
    runTest constantInlining =
      goldenPir (runQuote . runTestPass (\tc -> inlinePassSC 0 constantInlining tc def def)) pTerm
    withConstantInlining = True
    withoutConstantInlining = False

prop_inline
  :: BuiltinSemanticsVariant DefaultFun -> Property
prop_inline biVariant =
  withMaxSuccess numTestsForPassProp
    $ testPassProp
      runQuote
    $ \tc -> inlinePassSC 0 True tc def (def {_biSemanticsVariant = biVariant})
