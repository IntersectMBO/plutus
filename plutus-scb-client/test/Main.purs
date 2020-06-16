module Test.Main where

import Effect (Effect)
import Prelude
import JsonEncodingTests as JsonEncodingTests
import MainFrameTests as MainFrameTests
import Test.Unit.Main (runTest)

foreign import forDeps :: Effect Unit

main :: Effect Unit
main =
  runTest do
    JsonEncodingTests.all
    MainFrameTests.all
