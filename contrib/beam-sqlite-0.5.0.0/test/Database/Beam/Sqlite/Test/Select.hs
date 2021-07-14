{-# LANGUAGE OverloadedStrings #-}

module Database.Beam.Sqlite.Test.Select (tests) where

import Control.Exception
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit

import Data.Int (Int32)
import Data.Text (Text)
import Data.Time (LocalTime)

import Database.Beam
import Database.Beam.Sqlite

import Database.Beam.Sqlite.Test

import Database.SQLite.Simple (execute_)

tests :: TestTree
tests = testGroup "Selection tests"
  [ expectFail testExceptValues
  , testInRowValues
  , testInsertReturningColumnOrder -- In select tests because the bug was with the selects
  ]

data Pair f = Pair
  { _left :: C f Bool
  , _right :: C f Bool
  } deriving (Generic, Beamable)

testInRowValues :: TestTree
testInRowValues = testCase "IN with row values works" $
  withTestDb $ \conn -> do
    result <- runBeamSqlite conn $ runSelectReturningList $ select $ do
      let p :: forall ctx s. Pair (QGenExpr ctx Sqlite s)
          p = val_ $ Pair False False
      return $ p `in_` [p, p]
    assertEqual "result" [True] result

-- | Regression test for <https://github.com/haskell-beam/beam/issues/326 #326>
testExceptValues :: TestTree
testExceptValues = testCase "EXCEPT with VALUES works" $
  withTestDb $ \conn -> do
    result <- runBeamSqlite conn $ runSelectReturningList $ select $
      values_ [as_ @Bool $ val_ True, val_ False] `except_` values_ [val_ False]
    assertEqual "result" [True] result

data TestTableT f
  = TestTable
  { ttId :: C f Int32
  , ttFirstName :: C f Text
  , ttLastName  :: C f Text
  , ttAge       :: C f Int32
  , ttDateJoined :: C f LocalTime
  } deriving (Generic, Beamable)

deriving instance Show (TestTableT Identity)
deriving instance Eq (TestTableT Identity)

instance Table TestTableT where
  data PrimaryKey TestTableT f = TestTableKey (C f Int32)
    deriving (Generic, Beamable)
  primaryKey = TestTableKey <$> ttId

data TestTableDb entity
  = TestTableDb
  { dbTestTable :: entity (TableEntity TestTableT)
  } deriving (Generic, Database Sqlite)

testDatabase :: DatabaseSettings be TestTableDb
testDatabase = defaultDbSettings

testInsertReturningColumnOrder :: TestTree
testInsertReturningColumnOrder = testCase "runInsertReturningList with mismatching column order" $ do
  withTestDb $ \conn -> do
    execute_ conn "CREATE TABLE test_table ( date_joined TIMESTAMP NOT NULL, first_name TEXT NOT NULL, id INT PRIMARY KEY, age INT NOT NULL, last_name TEXT NOT NULL )"
    inserted <-
      runBeamSqlite conn $ runInsertReturningList $
      insert (dbTestTable testDatabase) $
      insertExpressions [ TestTable 0 (concat_ [ "j", "im" ]) "smith" 19 currentTimestamp_
                        , TestTable 1 "sally" "apple" ((val_ 56 + val_ 109) `div_` 5) currentTimestamp_
                        , TestTable 4 "blah" "blah" (-1) currentTimestamp_ ]

    let dateJoined = ttDateJoined (head inserted)

        expected = [ TestTable 0 "jim" "smith" 19 dateJoined
                   , TestTable 1 "sally" "apple" 33 dateJoined
                   , TestTable 4 "blah" "blah" (-1) dateJoined ]

    assertEqual "insert values" inserted expected
