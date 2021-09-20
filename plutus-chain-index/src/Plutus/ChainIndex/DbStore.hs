{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}
{-# options_ghc -Wno-missing-signatures #-}
{-

A beam-specific effect for writing to a beam database. Here we explicitly construct the
database schema for the data which we wish to store:

...

In particular this is specialised to 'Sqlite'; but it could be refactored to
work over a more general type, or changed to Postgres.

The schema we've opted for at present is a very simple one, with no ability to
track changes over time.

-}

module Plutus.ChainIndex.DbStore where

import           Cardano.BM.Trace                         (Trace, logDebug)
import           Control.Exception                        (try)
import           Control.Monad.Freer                      (Eff, LastMember, Member, type (~>))
import           Control.Monad.Freer.Error                (Error, throwError)
import           Control.Monad.Freer.TH                   (makeEffect)
import           Data.ByteString                          (ByteString)
import           Data.Kind                                (Constraint)
import           Data.Semigroup.Generic                   (GenericSemigroupMonoid (..))
import qualified Data.Text                                as Text
import           Database.Beam                            (Beamable, Columnar, Database, DatabaseEntity,
                                                           DatabaseSettings, FromBackendRow, Generic, Identity,
                                                           MonadIO (liftIO), SqlSelect, SqlUpdate, Table (..),
                                                           TableEntity, dbModification, insertValues, runInsert,
                                                           runSelectReturningList, runSelectReturningOne, runUpdate,
                                                           withDbModification)
import           Database.Beam.Backend.SQL                (BeamSqlBackendCanSerialize)
import           Database.Beam.Backend.SQL.BeamExtensions (BeamHasInsertOnConflict (anyConflict, insertOnConflict, onConflictDoNothing))
import           Database.Beam.Migrate                    (CheckedDatabaseSettings, defaultMigratableDbSettings,
                                                           renameCheckedEntity, unCheckDatabase)
import           Database.Beam.Schema.Tables              (FieldsFulfillConstraint)
import           Database.Beam.Sqlite                     (Sqlite, SqliteM, runBeamSqliteDebug)
import qualified Database.SQLite.Simple                   as Sqlite
import           Plutus.ChainIndex.ChainIndexError        (ChainIndexError (..))
import           Plutus.ChainIndex.ChainIndexLog          (ChainIndexLog (..))

data DatumRowT f
  = DatumRow
    { _datumRowHash  :: Columnar f ByteString
    , _datumRowDatum :: Columnar f ByteString
    } deriving (Generic, Beamable)

type DatumRow = DatumRowT Identity

instance Table DatumRowT where
  data PrimaryKey DatumRowT f = DatumRowId (Columnar f ByteString) deriving (Generic, Beamable)
  primaryKey = DatumRowId . _datumRowHash

data ScriptRowT f
  = ScriptRow
    { _scriptRowHash   :: Columnar f ByteString
    , _scriptRowScript :: Columnar f ByteString
    } deriving (Generic, Beamable)

type ScriptRow = ScriptRowT Identity

instance Table ScriptRowT where
  data PrimaryKey ScriptRowT f = ScriptRowId (Columnar f ByteString) deriving (Generic, Beamable)
  primaryKey = ScriptRowId . _scriptRowHash

data TxRowT f
  = TxRow
    { _txRowTxId :: Columnar f ByteString
    , _txRowTx   :: Columnar f ByteString
    } deriving (Generic, Beamable)

type TxRow = TxRowT Identity

instance Table TxRowT where
  data PrimaryKey TxRowT f = TxRowId (Columnar f ByteString) deriving (Generic, Beamable)
  primaryKey = TxRowId . _txRowTxId

data AddressRowT f
  = AddressRow
    { _addressRowHash    :: Columnar f ByteString
    , _addressRowAddress :: Columnar f ByteString
    } deriving (Generic, Beamable)

type AddressRow = AddressRowT Identity

instance Table AddressRowT where
  data PrimaryKey AddressRowT f = AddressRowId (Columnar f ByteString) (Columnar f ByteString) deriving (Generic, Beamable)
  primaryKey (AddressRow h a) = AddressRowId h a

data Db f = Db
    { datumRows   :: f (TableEntity DatumRowT)
    , scriptRows  :: f (TableEntity ScriptRowT)
    , txRows      :: f (TableEntity TxRowT)
    , addressRows :: f (TableEntity AddressRowT)
    }
    deriving (Generic, Database be)

type AllTables (c :: * -> Constraint) f = (c (f (TableEntity DatumRowT)), c (f (TableEntity ScriptRowT)), c (f (TableEntity TxRowT)), c (f (TableEntity AddressRowT)))
deriving via (GenericSemigroupMonoid (Db f)) instance AllTables Semigroup f => Semigroup (Db f)
deriving via (GenericSemigroupMonoid (Db f)) instance AllTables Monoid f => Monoid (Db f)

db :: DatabaseSettings Sqlite Db
db = unCheckDatabase checkedSqliteDb

checkedSqliteDb :: CheckedDatabaseSettings Sqlite Db
checkedSqliteDb = defaultMigratableDbSettings
  `withDbModification` dbModification
    { datumRows   = renameCheckedEntity (const "datums")
    , scriptRows  = renameCheckedEntity (const "scripts")
    , txRows      = renameCheckedEntity (const "txs")
    , addressRows = renameCheckedEntity (const "addresses")
    }

type BeamableSqlite table = (Beamable table, FieldsFulfillConstraint (BeamSqlBackendCanSerialize Sqlite) table)

-- | Effect for managing a beam-based database.
data DbStoreEffect r where
  -- | Insert a row into a table.
  AddRows
    ::
    ( BeamableSqlite table
    )
    => DatabaseEntity Sqlite Db (TableEntity table)
    -> [table Identity]
    -> DbStoreEffect ()

  UpdateRow
    ::
    ( Beamable table
    )
    => SqlUpdate Sqlite table
    -> DbStoreEffect ()

  SelectList
    ::
    ( FromBackendRow Sqlite a
    )
    => SqlSelect Sqlite a
    -> DbStoreEffect [a]

  SelectOne
    ::
    ( FromBackendRow Sqlite a
    )
    => SqlSelect Sqlite a
    -> DbStoreEffect (Maybe a)

handleDbStore ::
  forall effs.
  ( Member (Error ChainIndexError) effs
  , LastMember IO effs
  )
  => Trace IO ChainIndexLog
  -> Sqlite.Connection
  -> DbStoreEffect
  ~> Eff effs
handleDbStore trace conn eff = do
    case eff of
        AddRows table records ->
            runBeam trace conn $ insertBatched records
                where
                  -- Workaround for "too many SQL variables" sqlite error
                  insertBatched [] = pure ()
                  insertBatched (splitAt 400 -> (batch, rest)) = do
                      runInsert $ insertOnConflict table (insertValues batch) anyConflict onConflictDoNothing
                      insertBatched rest

        SelectList q -> runBeam trace conn $ runSelectReturningList q

        SelectOne q -> runBeam trace conn $ runSelectReturningOne q

        UpdateRow q -> runBeam trace conn $ runUpdate q

runBeam ::
  forall effs.
  ( Member (Error ChainIndexError) effs
  , LastMember IO effs
  )
  => Trace IO ChainIndexLog
  -> Sqlite.Connection
  -> SqliteM
  ~> Eff effs
runBeam trace conn action = do
    let traceSql = logDebug trace . SqlLog
    resultEither <- liftIO $ try $ runBeamSqliteDebug traceSql conn action
    case resultEither of
        -- 'Database.SQLite.Simple.ErrorError' corresponds to an SQL error or
        -- missing database. When this exception is raised, we suppose it's
        -- because the 'migrate' command was not executed before running the
        -- chain index server.
        Left e@(Sqlite.SQLError Sqlite.ErrorError _ _) -> do
            throwError $ MigrationNotDoneError $ Text.pack $ show e
        -- We handle and rethrow errors other than
        -- 'Database.SQLite.Simple.ErrorError'.
        Left e -> do
            throwError $ SqlError $ Text.pack $ show e
        Right v -> return v

makeEffect ''DbStoreEffect
