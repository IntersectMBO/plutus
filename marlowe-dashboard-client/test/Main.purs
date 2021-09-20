module Test.Main where

import Prologue
import Effect (Effect)
import Test.Unit.Main (runTest)

foreign import forDeps :: Effect Unit

main :: Effect Unit
main =
  runTest do
    pure unit
