module Timing.Spec (tests) where

import PlutusTx.Code (getPlcNoAnn)
import Timing.Disabled qualified as Disabled
import Timing.Enabled qualified as Enabled

import Test.Tasty.Extras (TestNested, embed, testNested)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestNested
tests =
  testNested
    "Timing"
    [ embed $
        testCase "timing preserves arithmetic UPLC" $
          getPlcNoAnn Enabled.increment @?= getPlcNoAnn Disabled.increment
    , embed $
        testCase "timing preserves conditional UPLC" $
          getPlcNoAnn Enabled.choose @?= getPlcNoAnn Disabled.choose
    ]
