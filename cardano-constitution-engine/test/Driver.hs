-- editorconfig-checker-disable-file
module Main where

import Cardano.Constitution.Config.Schema.UnitTests qualified as SchemaTests
import Cardano.Constitution.Validator.Empty.GoldenTests qualified as EmptyGoldenTests
import Test.Tasty

main :: IO ()
main = do
  let mainTest = testGroup "Testing Campaign"
        [ SchemaTests.tests
        , EmptyGoldenTests.tests
        ]
  defaultMain mainTest
