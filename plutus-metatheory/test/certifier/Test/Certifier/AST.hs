module Test.Certifier.AST where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant)
import UntypedPlutusCore
import UntypedPlutusCore.Transform.Certify.Hints qualified as Hints

import FFI.OptimizerTrace (mkFfiOptimizerTrace)
import MAlonzo.Code.Certifier (runCertifierMain)

import Data.Text.Encoding qualified as Text
import Test.Tasty
import Test.Tasty.HUnit

mkMockTracePair
  :: OptStage
  -> Term Name DefaultUni DefaultFun ()
  -> Term Name DefaultUni DefaultFun ()
  -> OptimizerTrace Name DefaultUni DefaultFun ()
mkMockTracePair stage before' after' =
  OptimizerTrace
    { optimizerTrace =
        [ Optimization
            { beforeAST = before'
            , stage = stage
            , hints = Hints.NoHints
            , afterAST = after'
            }
        ]
    }

runCertifierWithMockTrace
  :: OptimizerTrace Name DefaultUni DefaultFun ()
  -> IO Bool
runCertifierWithMockTrace trace = do
  let rawAgdaTrace = mkFfiOptimizerTrace trace
  case runCertifierMain rawAgdaTrace [] of
    Just (result, _report) -> pure result
    Nothing ->
      assertFailure "The certifier exited with an error."

testSuccess
  :: String
  -> OptStage
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
  -> OptStage
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

-- Helper functions for making lists of tests.
testSuccessItem
  :: ( String
     , OptStage
     , Term Name PLC.DefaultUni PLC.DefaultFun ()
     , Term Name PLC.DefaultUni PLC.DefaultFun ()
     )
  -> TestTree
testSuccessItem (name, stage, before, after) = testSuccess name stage before after

testFailureItem
  :: ( String
     , OptStage
     , Term Name PLC.DefaultUni PLC.DefaultFun ()
     , Term Name PLC.DefaultUni PLC.DefaultFun ()
     )
  -> TestTree
testFailureItem (name, stage, before, after) = testFailure name stage before after

testTrivialSuccess1 :: TestTree
testTrivialSuccess1 =
  testSuccess
    "Trivial success"
    FloatDelayStage
    (mkConstant () (1 :: Integer))
    (mkConstant () (1 :: Integer))

testTrivialFailure1 :: TestTree
testTrivialFailure1 =
  testFailure
    "Trivial failure"
    FloatDelayStage
    (mkConstant () (1 :: Integer))
    (mkConstant () (2 :: Integer))

testByteStringEqSuccess :: TestTree
testByteStringEqSuccess =
  testFailure
    "bytestrings expected to not be equal"
    FloatDelayStage
    (mkConstant () (Text.encodeUtf8 "foo"))
    (mkConstant () (Text.encodeUtf8 "bar"))

testByteStringEqFailure :: TestTree
testByteStringEqFailure =
  testSuccess
    "bytestrings expected to be equal"
    FloatDelayStage
    (mkConstant () (Text.encodeUtf8 "foo"))
    (mkConstant () (Text.encodeUtf8 "foo"))

astTests :: TestTree
astTests =
  testGroup
    "certifier ast tests"
    [ testTrivialSuccess1
    , testTrivialFailure1
    , testByteStringEqSuccess
    , testByteStringEqFailure
    ]
