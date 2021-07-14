module Main where

import Test.Tasty

import qualified Database.Beam.Sqlite.Test.Migrate as Migrate
import qualified Database.Beam.Sqlite.Test.Select as Select

main :: IO ()
main = defaultMain $ testGroup "beam-sqlite tests"
  [ Migrate.tests
  , Select.tests
  ]
