module Test.Main where

import Prologue
import Effect (Effect)
import Test.Data.Json.JsonNTuple (jsonNTupleTest)
import Test.Unit.Main (runTest)

foreign import forDeps :: Effect Unit

main :: Effect Unit
main =
  runTest do
    -- This test actually belongs to the web-common library, but there is no spago, nor
    -- test suite included there, so for the moment we run it as part of the marlowe-run app.
    jsonNTupleTest
