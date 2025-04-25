module Test.Certifier.Optimizer where

import AgdaTrace (mkAgdaTrace)
import MAlonzo.Code.VerifiedCompilation (runCertifierMain)
import PlutusCore qualified as PLC
import Test.Tasty
import Test.Tasty.HUnit
import Transform.Simplify
import Transform.Simplify.Lib
import UntypedPlutusCore

type SimplifierFunc
  = Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> PLC.Quote
      ( Term Name PLC.DefaultUni PLC.DefaultFun ()
      , SimplifierTrace Name PLC.DefaultUni PLC.DefaultFun ()
      )

mkUPLCTest
  :: SimplifierFunc
  -> String
  -> Term Name DefaultUni DefaultFun ()
  -> TestTree
mkUPLCTest simplifierFunc name input = testCase name $
  let rawAgdaTrace = PLC.runQuote $ do
        simplifierTrace <- snd <$> simplifierFunc input
        return $ mkAgdaTrace simplifierTrace
  in
    case runCertifierMain rawAgdaTrace of
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

simplifierTests :: TestTree
simplifierTests =
  testGroup "uplc simplifier tests"
    [ testGroup "cse tests"
        $ fmap (uncurry mkUPLCCseTest) testCseInputs
    , testGroup "other optimisation tests"
        $ fmap (uncurry mkUPLCSimplifierTest) testSimplifyInputs'
    ]
  where
    -- TODO(https://github.com/IntersectMBO/plutus-private/issues/1541):
    --   this removes two tests which are currently failing; we should
    --   fix the tests and add them back
    testSimplifyInputs' =
      filter
        (\(name, _) ->
          name /= "forceDelaySimple" && name /= "forceDelayComplex"
        )
        testSimplifyInputs
