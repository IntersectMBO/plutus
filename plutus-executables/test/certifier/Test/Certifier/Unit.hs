module Test.Certifier.Unit where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant)
import UntypedPlutusCore

import AgdaTrace (mkAgdaTrace)
import MAlonzo.Code.VerifiedCompilation (runCertifierMain)

import Test.Tasty
import Test.Tasty.HUnit

mkMockTracePair
  :: SimplifierStage
  -> Term Name DefaultUni DefaultFun ()
  -> Term Name DefaultUni DefaultFun ()
  -> SimplifierTrace Name DefaultUni DefaultFun ()
mkMockTracePair stage before' after' =
  SimplifierTrace
    { simplifierTrace =
        [ Simplification
            { beforeAST = before'
            , stage = stage
            , afterAST = after'
            }
        ]
    }

runCertifierWithMockTrace
  :: SimplifierTrace Name DefaultUni DefaultFun ()
  -> IO Bool
runCertifierWithMockTrace trace = do
  let rawAgdaTrace = mkAgdaTrace trace
  case runCertifierMain rawAgdaTrace of
    Just result -> pure result
    Nothing ->
      assertFailure "The certifier exited with an error."

testSuccess
  :: String
  -> SimplifierStage
  -> Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> TestTree
testSuccess testName st bf af =
  testCase testName $ do
    let trace = mkMockTracePair st bf af
    result <- runCertifierWithMockTrace trace
    assertBool
      "The certifier was expected to succeed."
      result

testFailure
  :: String
  -> SimplifierStage
  -> Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> TestTree
testFailure testName st bf af =
  testCase testName $ do
    let trace = mkMockTracePair st bf af
    result <- runCertifierWithMockTrace trace
    assertBool
      "The certifier was expected to fail."
      (not result)

testTrivialSuccess1 :: TestTree
testTrivialSuccess1 =
  testSuccess
    "Trivial success"
    FloatDelay
    (mkConstant () (1 :: Integer))
    (mkConstant () (1 :: Integer))

testTrivialFailure1 :: TestTree
testTrivialFailure1 =
  testFailure
    "Trivial failure"
    FloatDelay
    (mkConstant () (1 :: Integer))
    (mkConstant () (2 :: Integer))

unitTests :: TestTree
unitTests =
  testGroup "certifier unit tests"
    [ testTrivialSuccess1
    , testTrivialFailure1
    ]
