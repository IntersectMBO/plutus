module Main (main) where

import AsData.Budget.Spec qualified as AsData.Budget
import Blueprint.Tests qualified
import Budget.Spec qualified as Budget
import BuiltinCasing.Spec qualified as BuiltinCasing
import ByteStringLiterals.Spec qualified as ByteStringLiterals
import CallTrace.Spec qualified as CallTrace
import Inline.Spec qualified as Inline
import IntegerLiterals.NoStrict.NegativeLiterals.Spec qualified
import IntegerLiterals.NoStrict.NoNegativeLiterals.Spec qualified
import IntegerLiterals.Strict.NegativeLiterals.Spec qualified
import IntegerLiterals.Strict.NoNegativeLiterals.Spec qualified
import IsData.Budget.BuiltinCasing qualified as IsData.Budget.BuiltinCasing
import IsData.Budget.SoP qualified as IsData.Budget.SoP
import IsData.Spec qualified as IsData
import Lift.Spec qualified as Lift
import Optimization.Spec qualified as Optimization
import Plugin.Spec qualified as Plugin
import Recursion.Spec qualified as Recursion
import ShortCircuit.Spec qualified as ShortCircuit
import StageViolation.Spec qualified as StageViolation
import StdLib.Spec qualified as Lib
import Strictness.Spec qualified as Strictness
import TH.Spec qualified as TH
import Unicode.Spec qualified as Unicode
import Unsupported.Spec qualified as Unsupported

import Test.Tasty (TestTree, defaultMain)
import Test.Tasty.Extras (embed, runTestNested)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  runTestNested
    ["test"]
    [ Plugin.tests
    , IntegerLiterals.NoStrict.NegativeLiterals.Spec.tests
    , IntegerLiterals.NoStrict.NoNegativeLiterals.Spec.tests
    , IntegerLiterals.Strict.NegativeLiterals.Spec.tests
    , IntegerLiterals.Strict.NoNegativeLiterals.Spec.tests
    , embed ByteStringLiterals.tests
    , IsData.tests
    , IsData.Budget.SoP.tests
    , IsData.Budget.BuiltinCasing.tests
    , Lift.tests
    , TH.tests
    , Lib.tests
    , Budget.tests
    , AsData.Budget.tests
    , Inline.tests
    , Recursion.tests
    , Optimization.tests
    , Strictness.tests
    , Blueprint.Tests.tests
    , embed ShortCircuit.tests
    , embed Unicode.tests
    , StageViolation.tests
    , CallTrace.tests
    , BuiltinCasing.tests
    , Unsupported.tests
    ]
