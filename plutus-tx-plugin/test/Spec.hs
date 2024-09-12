module Main (main) where

import AsData.Budget.Spec qualified as AsData.Budget
import AssocMap.Spec qualified as AssocMap
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
import Test.Tasty (TestTree, defaultMain)
import Test.Tasty.Extras (embed, runTestNested)
import TH.Spec qualified as TH
import Unicode.Spec qualified as Unicode

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  runTestNested ["test"]
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
    , Strictness.tests
    , Blueprint.Tests.tests
    , AssocMap.goldenTests
    , embed ShortCircuit.tests
    , embed Unicode.tests
    , embed AssocMap.propertyTests
    ]
