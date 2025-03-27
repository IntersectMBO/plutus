module Main (main) where

-- import Array.Spec qualified as Array
-- import AsData.Budget.Spec qualified as AsData.Budget
-- import AssocMap.Spec qualified as AssocMap
-- import Blueprint.Tests qualified
import Budget.Spec qualified as Budget
-- import ByteStringLiterals.Spec qualified as ByteStringLiterals
-- import Inline.Spec qualified as Inline
-- import IntegerLiterals.NoStrict.NegativeLiterals.Spec qualified
-- import IntegerLiterals.NoStrict.NoNegativeLiterals.Spec qualified
-- import IntegerLiterals.Strict.NegativeLiterals.Spec qualified
-- import IntegerLiterals.Strict.NoNegativeLiterals.Spec qualified
-- import IsData.Spec qualified as IsData
-- import Lift.Spec qualified as Lift
-- import List.Spec qualified as List
-- import Optimization.Spec qualified as Optimization
-- import Plugin.Spec qualified as Plugin
-- import Recursion.Spec qualified as Recursion
-- import ShortCircuit.Spec qualified as ShortCircuit
-- import StdLib.Spec qualified as Lib
-- import Strictness.Spec qualified as Strictness
-- import TH.Spec qualified as TH
-- import Unicode.Spec qualified as Unicode

import Test.Tasty (TestTree, defaultMain)
import Test.Tasty.Extras (embed, runTestNested)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  runTestNested
    ["test"]
    [ Budget.tests

    ]
