{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
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

import           Codec.Serialise            (Serialise, deserialiseOrFail, serialise)
import           Data.ByteString            (ByteString)
import qualified Data.ByteString.Lazy       as BSL
import           Data.Coerce                (coerce)
import           Data.Either                (fromRight)
import           Data.Kind                  (Constraint)
import           Data.Semigroup.Generic     (GenericSemigroupMonoid (..))
import           Data.Word                  (Word64)
import           Database.Beam              (Beamable, Columnar, Database, DatabaseSettings, FromBackendRow, Generic,
                                             Identity, Table (..), TableEntity, dbModification, withDbModification)
import           Database.Beam.Migrate      (CheckedDatabaseSettings, defaultMigratableDbSettings, renameCheckedEntity,
                                             unCheckDatabase)
import           Database.Beam.Sqlite       (Sqlite)
import           Ledger                     (AssetClass, BlockId (..), Datum, DatumHash (..), MintingPolicy,
                                             MintingPolicyHash (..), Redeemer, RedeemerHash (..), Script,
                                             ScriptHash (..), Slot, StakeValidator, StakeValidatorHash (..), TxId (..),
                                             TxOutRef (..), Validator, ValidatorHash (..))
import           Plutus.ChainIndex.Tx       (ChainIndexTx)
import           Plutus.ChainIndex.Types    (BlockNumber (..), Tip (..))
import           Plutus.V1.Ledger.Api       (Credential)
import           PlutusTx.Builtins.Internal (BuiltinByteString (..))

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

data AssetClassRowT f = AssetClassRow
    { _assetClassRowAssetClass :: Columnar f ByteString
    , _assetClassRowOutRef     :: Columnar f ByteString
    } deriving (Generic, Beamable)

type AssetClassRow = AssetClassRowT Identity

instance Table AssetClassRowT where
    -- We also need an index on just the _assetClassRowAssetClass column, but the primary key index provides this
    -- as long as _assetClassRowAssetClass is the first column in the primary key.
    data PrimaryKey AssetClassRowT f = AssetClassRowId (Columnar f ByteString)
                                                       (Columnar f ByteString)
      deriving (Generic, Beamable)
    primaryKey (AssetClassRow c o) = AssetClassRowId c o

data TipRowT f = TipRow
    { _tipRowSlot        :: Columnar f Word64
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
    , assetClassRows     :: f (TableEntity AssetClassRowT)
    , tipRows            :: f (TableEntity TipRowT)
    , unspentOutputRows  :: f (TableEntity UnspentOutputRowT)
    , unmatchedInputRows :: f (TableEntity UnmatchedInputRowT)
    } deriving (Generic, Database be)

type AllTables (c :: * -> Constraint) f =
    ( c (f (TableEntity DatumRowT))
    , c (f (TableEntity ScriptRowT))
    , c (f (TableEntity TxRowT))
    , c (f (TableEntity AddressRowT))
    , c (f (TableEntity AssetClassRowT))
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
    , assetClassRows = renameCheckedEntity (const "asset_classes")
    , tipRows     = renameCheckedEntity (const "tips")
    , unspentOutputRows  = renameCheckedEntity (const "unspent_outputs")
    , unmatchedInputRows = renameCheckedEntity (const "unmatched_inputs")
    }

-- | Instances of @HasDbType@ can be converted to types that can be stored in the database.
-- `toDbValue` and `fromDbValue` must be inverses of each other.
class FromBackendRow Sqlite (DbType a) => HasDbType a where
    type DbType a
    toDbValue :: a -> DbType a
    fromDbValue :: DbType a -> a

instance HasDbType ByteString where
    type DbType ByteString = ByteString
    toDbValue = id
    fromDbValue = id

deriving via ByteString instance HasDbType DatumHash
deriving via ByteString instance HasDbType ValidatorHash
deriving via ByteString instance HasDbType MintingPolicyHash
deriving via ByteString instance HasDbType RedeemerHash
deriving via ByteString instance HasDbType StakeValidatorHash
deriving via ByteString instance HasDbType TxId
deriving via ByteString instance HasDbType BlockId
deriving via ByteString instance HasDbType ScriptHash

newtype Serialisable a = Serialisable { getSerialisable :: a }
instance Serialise a => HasDbType (Serialisable a) where
    type DbType (Serialisable a) = ByteString
    fromDbValue
        = Serialisable
        . fromRight (error "Deserialisation failed. Delete your chain index database and resync.")
        . deserialiseOrFail
        . BSL.fromStrict
    toDbValue = BSL.toStrict . serialise . getSerialisable

deriving via Serialisable Datum instance HasDbType Datum
deriving via Serialisable MintingPolicy instance HasDbType MintingPolicy
deriving via Serialisable Redeemer instance HasDbType Redeemer
deriving via Serialisable StakeValidator instance HasDbType StakeValidator
deriving via Serialisable Validator instance HasDbType Validator
deriving via Serialisable ChainIndexTx instance HasDbType ChainIndexTx
deriving via Serialisable TxOutRef instance HasDbType TxOutRef
deriving via Serialisable Credential instance HasDbType Credential
deriving via Serialisable AssetClass instance HasDbType AssetClass
deriving via Serialisable Script instance HasDbType Script

instance HasDbType Slot where
    type DbType Slot = Word64 -- In Plutus Slot is Integer, but in the Cardano API it is Word64, so this is safe
    toDbValue = fromIntegral
    fromDbValue = fromIntegral

instance HasDbType BlockNumber where
    type DbType BlockNumber = Word64
    toDbValue = coerce
    fromDbValue = coerce

instance HasDbType Tip where
    type DbType Tip = Maybe TipRow
    toDbValue TipAtGenesis   = Nothing
    toDbValue (Tip sl bi bn) = Just (TipRow (toDbValue sl) (toDbValue bi) (toDbValue bn))
    fromDbValue Nothing                  = TipAtGenesis
    fromDbValue (Just (TipRow sl bi bn)) = Tip (fromDbValue sl) (fromDbValue bi) (fromDbValue bn)

instance HasDbType (DatumHash, Datum) where
    type DbType (DatumHash, Datum) = DatumRow
    toDbValue (hash, datum) = DatumRow (toDbValue hash) (toDbValue datum)
    fromDbValue (DatumRow hash datum) = (fromDbValue hash, fromDbValue datum)

instance HasDbType (ScriptHash, Script) where
    type DbType (ScriptHash, Script) = ScriptRow
    toDbValue (hash, script) = ScriptRow (toDbValue hash) (toDbValue script)
    fromDbValue (ScriptRow hash script) = (fromDbValue hash, fromDbValue script)

instance HasDbType (RedeemerHash, Redeemer) where
    type DbType (RedeemerHash, Redeemer) = ScriptRow
    toDbValue (hash, script) = ScriptRow (toDbValue hash) (toDbValue script)
    fromDbValue (ScriptRow hash script) = (fromDbValue hash, fromDbValue script)

instance HasDbType (TxId, ChainIndexTx) where
    type DbType (TxId, ChainIndexTx) = TxRow
    toDbValue (txId, tx) = TxRow (toDbValue txId) (toDbValue tx)
    fromDbValue (TxRow txId tx) = (fromDbValue txId, fromDbValue tx)

instance HasDbType (Credential, TxOutRef) where
    type DbType (Credential, TxOutRef) = AddressRow
    toDbValue (cred, outRef) = AddressRow (toDbValue cred) (toDbValue outRef)
    fromDbValue (AddressRow cred outRef) = (fromDbValue cred, fromDbValue outRef)

instance HasDbType (AssetClass, TxOutRef) where
    type DbType (AssetClass, TxOutRef) = AssetClassRow
    toDbValue (ac, outRef) = AssetClassRow (toDbValue ac) (toDbValue outRef)
    fromDbValue (AssetClassRow ac outRef) = (fromDbValue ac, fromDbValue outRef)
