module Main (main) where

import Budget.Spec qualified as Budget
import IsData.Spec qualified as IsData
import Lift.Spec qualified as Lift
import Optimization.Spec qualified as Optimization
import Plugin.Spec qualified as Plugin
import StdLib.Spec qualified as Lib
import Strictness.Spec qualified as Strictness
import TH.Spec qualified as TH

import Test.Tasty
import Test.Tasty.Extras

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

tests :: TestNested
tests = testGroup "tests" <$> sequence [
    Plugin.tests
  , IsData.tests
  , Lift.tests
  , TH.tests
  , Lib.tests
  , Budget.tests
  , Optimization.tests
  , Strictness.tests
  ]
