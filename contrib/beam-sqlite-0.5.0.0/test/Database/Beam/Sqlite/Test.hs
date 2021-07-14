module Database.Beam.Sqlite.Test where

import Control.Exception
import Database.SQLite.Simple
import Test.Tasty.HUnit

withTestDb :: (Connection -> IO a) -> IO a
withTestDb = flip catch asFailure . bracket (open ":memory:") close
  where asFailure (e :: SomeException) = assertFailure $ show e
