module Regressions
    (
      tests
    ) where

import Data.Double.Conversion.Text (toShortest)
import Test.HUnit (Assertion, assertEqual)
import Data.Text (unpack)
import Numeric (showFFloat)
import qualified Test.Framework as F
import qualified Test.Framework.Providers.HUnit as F

toShortest_overflow :: Assertion
toShortest_overflow = do
  let val = -2.9658956854023756e-5
  assertEqual "rendering a long number doesn't crash"
              (showFFloat Nothing val "") (unpack (toShortest val))

tests :: F.Test
tests = F.testGroup "Regressions"
  [
    F.testCase "toShortest_overflow" toShortest_overflow
  ]
