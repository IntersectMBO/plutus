module Test.Certifier.AST where

import PlutusCore qualified as PLC
import PlutusCore.Data qualified as Data
import PlutusCore.MkPlc (mkConstant)

import Data.ByteString (ByteString)
import Data.Text (Text)
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

bs :: Text -> ByteString
bs = Text.encodeUtf8

-- The following tests exercise the runtime decidable equality of the
-- postulated builtin types (see "Equality of postulated types" in the
-- metatheory's Utils module): each unequal pair must make the certifier
-- reject the trace, and each equal pair must make it accept.

testByteStringEq :: TestTree
testByteStringEq =
  testSuccess
    "equal bytestring constants are accepted"
    FloatDelayStage
    (mkConstant () (bs "foo"))
    (mkConstant () (bs "foo"))

testByteStringNeq :: TestTree
testByteStringNeq =
  testFailure
    "unequal bytestring constants are rejected"
    FloatDelayStage
    (mkConstant () (bs "foo"))
    (mkConstant () (bs "bar"))

testDataEq :: TestTree
testDataEq =
  testSuccess
    "equal Data constants are accepted"
    FloatDelayStage
    (mkConstant () (Data.B (bs "foo")))
    (mkConstant () (Data.B (bs "foo")))

testDataNeq :: TestTree
testDataNeq =
  testFailure
    "unequal Data constants are rejected"
    FloatDelayStage
    (mkConstant () (Data.B (bs "foo")))
    (mkConstant () (Data.B (bs "bar")))

testNestedDataNeq :: TestTree
testNestedDataNeq =
  testFailure
    "Data constants differing in a nested bytestring leaf are rejected"
    FloatDelayStage
    (mkConstant () (Data.Constr 0 [Data.List [Data.I 1, Data.B (bs "foo")]]))
    (mkConstant () (Data.Constr 0 [Data.List [Data.I 1, Data.B (bs "bar")]]))

testByteStringListEq :: TestTree
testByteStringListEq =
  testSuccess
    "equal bytestring list constants are accepted"
    FloatDelayStage
    (mkConstant () [bs "foo", bs "bar"])
    (mkConstant () [bs "foo", bs "bar"])

testByteStringListNeq :: TestTree
testByteStringListNeq =
  testFailure
    "unequal bytestring list constants are rejected"
    FloatDelayStage
    (mkConstant () [bs "foo", bs "bar"])
    (mkConstant () [bs "foo", bs "baz"])

astTests :: TestTree
astTests =
  testGroup
    "certifier ast tests"
    [ testTrivialSuccess1
    , testTrivialFailure1
    , testByteStringEq
    , testByteStringNeq
    , testDataEq
    , testDataNeq
    , testNestedDataNeq
    , testByteStringListEq
    , testByteStringListNeq
    ]
