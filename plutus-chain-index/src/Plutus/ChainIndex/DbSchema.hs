{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
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

module Plutus.ChainIndex.DbSchema where

import           Data.ByteString        (ByteString)
import           Data.Kind              (Constraint)
import           Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import           Data.Word              (Word64)
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

data TipRowT f = TipRow
    { _tipRowSlot        :: Columnar f Word64 -- In Plutus Slot is Integer, but in the Cardano API it is Word64, so this is safe
    , _tipRowBlockId     :: Columnar f ByteString
    , _tipRowBlockNumber :: Columnar f Word64
    } deriving (Generic, Beamable)

type TipRow = TipRowT Identity

instance Table TipRowT where
    data PrimaryKey TipRowT f = TipRowId { unTipRowId :: Columnar f Word64 } deriving (Generic, Beamable)
    primaryKey = TipRowId . _tipRowSlot

{-
The UnspentOutputRow and UnmatchedInputRow tables represent the TxUtxoBalance part of the UtxoState data on disk.
In particular the tip is the one that produced the utxo, except for the rows
that come from transactions that can no longer be rolled back:
In the UtxoState data that can no longer be rolled back are combined in a single TxUtxoBalance value.
The tip in those cases is the most recent tip that can no longer be rolled back.
(This is an automatic result of the Monoid instance on TxUtxoBalance, and is a bit weird when spelled
out as a database design, but the disk state and in memory state should be kept in sync.)
-}

data UnspentOutputRowT f = UnspentOutputRow
    { _unspentOutputRowTip    :: PrimaryKey TipRowT f
    , _unspentOutputRowOutRef :: Columnar f ByteString
    } deriving (Generic, Beamable)

type UnspentOutputRow = UnspentOutputRowT Identity

instance Table UnspentOutputRowT where
    data PrimaryKey UnspentOutputRowT f = UnspentOutputRowId (PrimaryKey TipRowT f) (Columnar f ByteString) deriving (Generic, Beamable)
    primaryKey (UnspentOutputRow t o) = UnspentOutputRowId t o

data UnmatchedInputRowT f = UnmatchedInputRow
    { _unmatchedInputRowTip    :: PrimaryKey TipRowT f
    , _unmatchedInputRowOutRef :: Columnar f ByteString
    } deriving (Generic, Beamable)

type UnmatchedInputRow = UnmatchedInputRowT Identity

instance Table UnmatchedInputRowT where
    data PrimaryKey UnmatchedInputRowT f = UnmatchedInputRowId (PrimaryKey TipRowT f) (Columnar f ByteString) deriving (Generic, Beamable)
    primaryKey (UnmatchedInputRow t o) = UnmatchedInputRowId t o

data Db f = Db
    { datumRows          :: f (TableEntity DatumRowT)
    , scriptRows         :: f (TableEntity ScriptRowT)
    , txRows             :: f (TableEntity TxRowT)
    , addressRows        :: f (TableEntity AddressRowT)
    , tipRows            :: f (TableEntity TipRowT)
    , unspentOutputRows  :: f (TableEntity UnspentOutputRowT)
    , unmatchedInputRows :: f (TableEntity UnmatchedInputRowT)
    } deriving (Generic, Database be)

type AllTables (c :: * -> Constraint) f =
    ( c (f (TableEntity DatumRowT))
    , c (f (TableEntity ScriptRowT))
    , c (f (TableEntity TxRowT))
    , c (f (TableEntity AddressRowT))
    , c (f (TableEntity TipRowT))
    , c (f (TableEntity UnspentOutputRowT))
    , c (f (TableEntity UnmatchedInputRowT))
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
    , tipRows     = renameCheckedEntity (const "tips")
    , unspentOutputRows  = renameCheckedEntity (const "unspent_outputs")
    , unmatchedInputRows = renameCheckedEntity (const "unmatched_inputs")
    }
