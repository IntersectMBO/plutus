module Database.Beam.Sqlite.Test.Migrate (tests) where

import Database.SQLite.Simple
import Test.Tasty
import Test.Tasty.HUnit

import Database.Beam
import Database.Beam.Sqlite
import Database.Beam.Sqlite.Migrate
import Database.Beam.Migrate
import Database.Beam.Migrate.Simple

import Database.Beam.Sqlite.Test

tests :: TestTree
tests = testGroup "Migration tests"
  [ verifiesPrimaryKey
  , verifiesNoPrimaryKey
  ]

newtype WithPkT f = WithPkT
  { _with_pk_value :: C f Bool
  } deriving (Generic, Beamable)

instance Table WithPkT where
  newtype PrimaryKey WithPkT f = Pk (C f Bool)
    deriving (Generic, Beamable)

  primaryKey = Pk . _with_pk_value

data WithPkDb entity = WithPkDb
  { _with_pk :: entity (TableEntity WithPkT)
  } deriving (Generic, Database Sqlite)

withPkDbChecked :: CheckedDatabaseSettings Sqlite WithPkDb
withPkDbChecked = defaultMigratableDbSettings

newtype WithoutPkT f = WithoutPkT
  { _without_pk_value :: C f Bool
  } deriving (Generic, Beamable)

instance Table WithoutPkT where
  data PrimaryKey WithoutPkT f = NoPk
    deriving (Generic, Beamable)

  primaryKey _ = NoPk

data WithoutPkDb entity = WithoutPkDb
  { _without_pk :: entity (TableEntity WithoutPkT)
  } deriving (Generic, Database Sqlite)

withoutPkDbChecked :: CheckedDatabaseSettings Sqlite WithoutPkDb
withoutPkDbChecked = defaultMigratableDbSettings

verifiesPrimaryKey :: TestTree
verifiesPrimaryKey = testCase "verifySchema correctly detects primary key" $
  withTestDb $ \conn -> do
    execute_ conn "create table with_pk (with_pk_value bool not null primary key)"
    testVerifySchema conn withPkDbChecked

verifiesNoPrimaryKey :: TestTree
verifiesNoPrimaryKey = testCase "verifySchema correctly handles table with no primary key" $
  withTestDb $ \conn -> do
    execute_ conn "create table without_pk (without_pk_value bool not null)"
    testVerifySchema conn withoutPkDbChecked

testVerifySchema
  :: Database Sqlite db
  => Connection -> CheckedDatabaseSettings Sqlite db -> Assertion
testVerifySchema conn db =
  runBeamSqlite conn (verifySchema migrationBackend db) >>= \case
    VerificationSucceeded -> return ()
    VerificationFailed failures ->
      fail $ "Verification failed: " ++ show failures
