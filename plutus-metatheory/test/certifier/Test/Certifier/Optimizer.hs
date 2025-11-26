module Test.Certifier.Optimizer where

import FFI.SimplifierTrace (mkFfiSimplifierTrace)
import MAlonzo.Code.VerifiedCompilation (runCertifierMain)
import PlutusCore qualified as PLC
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)
import Transform.Simplify.Lib (testCse, testSimplify)
import Transform.Simplify.Spec (testCseInputs, testSimplifyInputs)
import UntypedPlutusCore (DefaultFun, DefaultUni, Name, SimplifierTrace, Term)

type SimplifierFunc =
  Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> PLC.Quote
       ( Term Name PLC.DefaultUni PLC.DefaultFun ()
       , SimplifierTrace Name PLC.DefaultUni PLC.DefaultFun ()
       )

mkUPLCTest
  :: SimplifierFunc
  -> String
  -> Term Name DefaultUni DefaultFun ()
  -> TestTree
mkUPLCTest simplifierFunc name input =
  testCase name $
    let rawAgdaTrace = PLC.runQuote $ do
          simplifierTrace <- snd <$> simplifierFunc input
          return $ mkFfiSimplifierTrace simplifierTrace
     in case runCertifierMain rawAgdaTrace of
          Just result ->
            assertBool "The certifier returned false." result
          Nothing ->
            assertFailure "The certifier exited with an error."

mkUPLCSimplifierTest
  :: String
  -> Term Name DefaultUni DefaultFun ()
  -> TestTree
mkUPLCSimplifierTest = mkUPLCTest testSimplify

mkUPLCCseTest
  :: String
  -> Term Name DefaultUni DefaultFun ()
  -> TestTree
mkUPLCCseTest = mkUPLCTest testCse

optimizerTests :: TestTree
optimizerTests =
  testGroup
    "uplc optimizer tests"
    [ testGroup "cse tests" $
        fmap (uncurry mkUPLCCseTest) testCseInputs
    , testGroup "simplification tests" $
        fmap (uncurry mkUPLCSimplifierTest) testSimplifyInputs
    ]
