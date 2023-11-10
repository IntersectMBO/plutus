-- editorconfig-checker-disable-file
module Main (main) where

import AsData.Budget.Spec qualified as AsData.Budget
import Budget.Spec qualified as Budget
import IntegerLiterals.NoStrict.NegativeLiterals.Spec qualified as IntegerLiterals.NoStrict.NegativeLiterals
import IntegerLiterals.NoStrict.NoNegativeLiterals.Spec qualified as IntegerLiterals.NoStrict.NoNegativeLiterals
import IntegerLiterals.Strict.NegativeLiterals.Spec qualified as IntegerLiterals.Strict.NegativeLiterals
import IntegerLiterals.Strict.NoNegativeLiterals.Spec qualified as IntegerLiterals.Strict.NoNegativeLiterals
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
tests =
  testGroup "tests"
    <$> sequence
      [ Plugin.tests
      , IntegerLiterals.NoStrict.NegativeLiterals.tests
      , IntegerLiterals.NoStrict.NoNegativeLiterals.tests
      , IntegerLiterals.Strict.NegativeLiterals.tests
      , IntegerLiterals.Strict.NoNegativeLiterals.tests
      , IsData.tests
      , Lift.tests
      , TH.tests
      , Lib.tests
      , Budget.tests
      , AsData.Budget.tests
      , Optimization.tests
      , Strictness.tests
      ]
