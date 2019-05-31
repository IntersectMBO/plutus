module Test.Main where

import Prelude

import AjaxUtilsTests as AjaxUtilsTests
import ChainTests as ChainTests
import CursorTests as CursorTests
import Data.Array.ExtraTests as Data.Array.ExtraTests
import Data.String.ExtraTests as Data.String.ExtraTests
import Effect (Effect)
import GistsTests as GistsTests
import Ledger.ExtraTests as Ledger.ExtraTests
import MainFrameTests as MainFrameTests
import Test.Unit.Main (runTest)
import TypesTests as TypesTests

foreign import forDeps :: Effect Unit

main :: Effect Unit
main = runTest do
  AjaxUtilsTests.all
  ChainTests.all
  CursorTests.all
  Data.Array.ExtraTests.all
  Data.String.ExtraTests.all
  GistsTests.all
  Ledger.ExtraTests.all
  MainFrameTests.all
  TypesTests.all
