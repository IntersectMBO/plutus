module Main (main) where

import AsData.Budget.Spec qualified as AsData.Budget
import AssocList.Spec qualified as AssocList
import Blueprint.Tests qualified
import Budget.Spec qualified as Budget
import IntegerLiterals.NoStrict.NegativeLiterals.Spec qualified
import IntegerLiterals.NoStrict.NoNegativeLiterals.Spec qualified
import IntegerLiterals.Strict.NegativeLiterals.Spec qualified
import IntegerLiterals.Strict.NoNegativeLiterals.Spec qualified
import IsData.Spec qualified as IsData
import Lift.Spec qualified as Lift
import Optimization.Spec qualified as Optimization
import Plugin.Spec qualified as Plugin
import ShortCircuit.Spec qualified as ShortCircuit
import StdLib.Spec qualified as Lib
import Strictness.Spec qualified as Strictness
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.Extras (TestNested, runTestNestedIn)
import TH.Spec qualified as TH
import Unicode.Spec qualified as Unicode

main :: IO ()
main = defaultMain $ testGroup "" [runTestNestedIn ["test"] tests, AssocList.propertyTests]

tests :: TestNested
tests =
  testGroup "tests"
    <$> sequence
      [ Plugin.tests
      , IntegerLiterals.NoStrict.NegativeLiterals.Spec.tests
      , IntegerLiterals.NoStrict.NoNegativeLiterals.Spec.tests
      , IntegerLiterals.Strict.NegativeLiterals.Spec.tests
      , IntegerLiterals.Strict.NoNegativeLiterals.Spec.tests
      , IsData.tests
      , Lift.tests
      , TH.tests
      , Lib.tests
      , Budget.tests
      , AsData.Budget.tests
      , Optimization.tests
      , pure ShortCircuit.tests
      , Strictness.tests
      , Blueprint.Tests.goldenTests
      , pure Unicode.tests
      , AssocList.goldenTests
      ]
