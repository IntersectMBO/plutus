-- | Timing, with or without forcing, must not change the generated UPLC.
module Timing.Spec (tests) where

import PlutusTx.Code (getPlcNoAnn)
import Timing.Disabled qualified as Disabled
import Timing.Enabled qualified as Enabled
import Timing.Unforced qualified as Unforced

import Test.Tasty.Extras (TestNested, embed, testNested)
import Test.Tasty.HUnit (testCase, (@?=))

-- | Compare each timed fixture against the untimed one.
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
    , embed $
        testCase "non-forcing timing preserves arithmetic UPLC" $
          getPlcNoAnn Unforced.increment @?= getPlcNoAnn Disabled.increment
    , embed $
        testCase "non-forcing timing preserves conditional UPLC" $
          getPlcNoAnn Unforced.choose @?= getPlcNoAnn Disabled.choose
    ]
