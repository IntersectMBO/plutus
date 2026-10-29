module Test.Certifier.Optimizer where

import FFI.OptimizerTrace (mkFfiOptimizerTrace)
import MAlonzo.Code.Certifier (runCertifierMain)
import PlutusCore qualified as PLC
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)
import Transform.Simplify.CaseOfCase.Spec qualified as COC
import Transform.Simplify.Lib (testCse, testOptimize)
import Transform.Simplify.Spec (testCseInputs, testSimplifyInputs)
import UntypedPlutusCore
  ( CseWhichSubterms (..)
  , DefaultFun
  , DefaultUni
  , Name
  , OptimizerTrace
  , Term
  )

type SimplifierFunc =
  Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> PLC.Quote
       ( Term Name PLC.DefaultUni PLC.DefaultFun ()
       , OptimizerTrace Name PLC.DefaultUni PLC.DefaultFun ()
       )

mkUPLCTest
  :: SimplifierFunc
  -> String
  -> Term Name DefaultUni DefaultFun ()
  -> TestTree
mkUPLCTest simplifierFunc name input =
  testCase name $
    let rawAgdaTrace = PLC.runQuote $ do
          optimizerTrace <- snd <$> simplifierFunc input
          return $ mkFfiOptimizerTrace optimizerTrace
     in case runCertifierMain rawAgdaTrace [] of
          Just (result, _report) ->
            assertBool "The certifier returned false." result
          Nothing ->
            assertFailure "The certifier exited with an error."

mkUPLCSimplifierTest
  :: String
  -> Term Name DefaultUni DefaultFun ()
  -> TestTree
mkUPLCSimplifierTest = mkUPLCTest testOptimize

mkUPLCCseTest
  :: CseWhichSubterms
  -> String
  -> Term Name DefaultUni DefaultFun ()
  -> TestTree
mkUPLCCseTest which = mkUPLCTest (testCse which)

optimizerTests :: TestTree
optimizerTests =
  testGroup
    "uplc optimizer tests"
    $ [
        -- Reuse the simplifier test inputs from plutus-core `Transform.Simplify.Spec`
        -- and make sure they pass the certifier
        testGroup "certify simplifier tests" $
          fmap (uncurry mkUPLCSimplifierTest) testSimplifyInputs
      , -- Also reuse CSE test inputs, in both subterm modes
        testGroup "cse tests" $
          [ testGroup (show whichSubterms) $
              fmap (uncurry (mkUPLCCseTest whichSubterms)) testCseInputs
          | whichSubterms <- [AllSubterms, ExcludeWorkFree]
          ]
      , -- Also the case-of-case inputs
        testGroup "case-of-case" $
          fmap (uncurry mkUPLCSimplifierTest) COC.inputs
      ]
