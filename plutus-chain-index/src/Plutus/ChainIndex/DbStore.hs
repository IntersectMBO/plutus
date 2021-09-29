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

Here we explicitly construct the
database schema for the data which we wish to store:

- Datums
- Scripts
- Transactions
- Transaction output references indexed by address

-}

module Plutus.ChainIndex.DbStore where

import           Cardano.BM.Trace                         (Trace, logDebug)
import           Control.Concurrent                       (threadDelay)
import           Control.Exception                        (try)
import           Control.Monad.Freer                      (Eff, LastMember, Member, type (~>))
import           Control.Monad.Freer.Error                (Error, throwError)
import           Control.Monad.Freer.TH                   (makeEffect)
import           Data.ByteString                          (ByteString)
import           Data.Foldable                            (traverse_)
import           Data.Kind                                (Constraint)
import           Data.Semigroup.Generic                   (GenericSemigroupMonoid (..))
import qualified Data.Text                                as Text
import           Data.Word                                (Word64)
import           Database.Beam                            (Beamable, Columnar, Database, DatabaseEntity,
                                                           DatabaseSettings, FromBackendRow, Generic, Identity,
                                                           MonadIO (liftIO), SqlDelete, SqlSelect, SqlUpdate,
                                                           Table (..), TableEntity, dbModification, insertValues,
                                                           runDelete, runInsert, runSelectReturningList,
                                                           runSelectReturningOne, runUpdate, withDbModification)
import           Database.Beam.Backend.SQL                (BeamSqlBackendCanSerialize)
import           Database.Beam.Backend.SQL.BeamExtensions (BeamHasInsertOnConflict (anyConflict, insertOnConflict, onConflictDoNothing))
import           Database.Beam.Migrate                    (CheckedDatabaseSettings, defaultMigratableDbSettings,
                                                           renameCheckedEntity, unCheckDatabase)
import           Database.Beam.Schema.Tables              (FieldsFulfillConstraint)
import           Database.Beam.Sqlite                     (Sqlite, SqliteM, runBeamSqliteDebug)
import qualified Database.SQLite.Simple                   as Sqlite
import           Plutus.ChainIndex.ChainIndexError        (ChainIndexError (..))
import           Plutus.ChainIndex.ChainIndexLog          (ChainIndexLog (..))
import           Data.ByteString        (ByteString)
import           Data.Int               (Int16, Int64)
import           Data.Kind              (Constraint)
import           Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import           Database.Beam          (Beamable, Columnar, Database, DatabaseSettings, Generic, Identity, Table (..),
                                         TableEntity, dbModification, withDbModification)
import           Database.Beam.Migrate  (CheckedDatabaseSettings, defaultMigratableDbSettings, renameCheckedEntity,
                                         unCheckDatabase)
import           Database.Beam.Sqlite   (Sqlite)

data DatumRowT f = DatumRow
    { _datumRowHash  :: Columnar f ByteString
    , _datumRowDatum :: Columnar f ByteString
    } deriving (Generic, Beamable)

type DatumRow = DatumRowT Identity

instance Table DatumRowT where
    data PrimaryKey DatumRowT f = DatumRowId (Columnar f ByteString) deriving (Generic, Beamable)
    primaryKey = DatumRowId . _datumRowHash

data ScriptRowT f = ScriptRow
    { _scriptRowHash   :: Columnar f ByteString
    , _scriptRowScript :: Columnar f ByteString
    } deriving (Generic, Beamable)

type ScriptRow = ScriptRowT Identity

instance Table ScriptRowT where
    data PrimaryKey ScriptRowT f = ScriptRowId (Columnar f ByteString) deriving (Generic, Beamable)
    primaryKey = ScriptRowId . _scriptRowHash

data TxRowT f = TxRow
    { _txRowTxId :: Columnar f ByteString
    , _txRowTx   :: Columnar f ByteString
    } deriving (Generic, Beamable)

type TxRow = TxRowT Identity

instance Table TxRowT where
    data PrimaryKey TxRowT f = TxRowId (Columnar f ByteString) deriving (Generic, Beamable)
    primaryKey = TxRowId . _txRowTxId

data AddressRowT f = AddressRow
    { _addressRowCred   :: Columnar f ByteString
    , _addressRowOutRef :: Columnar f ByteString
    } deriving (Generic, Beamable)

type AddressRow = AddressRowT Identity

instance Table AddressRowT where
    -- We also need an index on just the _addressRowCred column, but the primary key index provides this
    -- as long as _addressRowCred is the first column in the primary key.
    data PrimaryKey AddressRowT f = AddressRowId (Columnar f ByteString) (Columnar f ByteString) deriving (Generic, Beamable)
    primaryKey (AddressRow c o) = AddressRowId c o

data UtxoRowT f = UtxoRow
    { _utxoRowSlot        :: Columnar f Word64 -- In Plutus Slot is Integer, but in the Cardano API it is Word64, so this is safe
    , _utxoRowBlockId     :: Columnar f ByteString
    , _utxoRowBlockNumber :: Columnar f Word64
    , _utxoRowBalance     :: Columnar f ByteString
    } deriving (Generic, Beamable)

type UtxoRow = UtxoRowT Identity

instance Table UtxoRowT where
    data PrimaryKey UtxoRowT f = UtxoRowId (Columnar f Word64) deriving (Generic, Beamable)
    primaryKey = UtxoRowId . _utxoRowSlot

data Db f = Db
    { datumRows   :: f (TableEntity DatumRowT)
    , scriptRows  :: f (TableEntity ScriptRowT)
    , txRows      :: f (TableEntity TxRowT)
    , addressRows :: f (TableEntity AddressRowT)
    , utxoRows    :: f (TableEntity UtxoRowT)
    } deriving (Generic, Database be)

type AllTables (c :: * -> Constraint) f =
    ( c (f (TableEntity DatumRowT))
    , c (f (TableEntity ScriptRowT))
    , c (f (TableEntity TxRowT))
    , c (f (TableEntity AddressRowT))
    , c (f (TableEntity UtxoRowT))
    )
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
    , utxoRows    = renameCheckedEntity (const "utxo")
    }
