module Main (main) where

import Budget.Spec qualified as Budget
import IsData.Spec qualified as IsData
import Lift.Spec qualified as Lift
import Plugin.Spec qualified as Plugin
import StdLib.Spec qualified as Lib
import TH.Spec qualified as TH

import Common

import Test.Tasty

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
  ]
