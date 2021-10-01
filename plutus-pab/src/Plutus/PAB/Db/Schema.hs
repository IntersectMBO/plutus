{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
{-# options_ghc -Wno-missing-signatures #-}

{-

Here we explicitly construct the database schema for the effects which we wish
to store:

- 'Pluts.PAB.Effects.Contract.ContractStore' effect
- 'Pluts.PAB.Effects.Contract.ContractDefinitionStore' effect

The schema we've opted for at present is a very simple one, with no ability to
track changes over time.

-}

module Plutus.PAB.Db.Schema where
import           Data.Text             (Text)
import           Database.Beam
import           Database.Beam.Migrate
import           Database.Beam.Sqlite  (Sqlite)

data ContractInstanceT f
  = ContractInstance
    { _contractInstanceId         :: Columnar f Text
    , _contractInstanceContractId :: Columnar f Text
    , _contractInstanceWallet     :: Columnar f Text -- Note: Sqlite doesn't have a integer type large enough.
    , _contractInstanceState      :: Columnar f (Maybe Text)
    , _contractInstanceActive     :: Columnar f Bool
    } deriving (Generic, Beamable)

ContractInstance
  (LensFor contractInstanceId)
  (LensFor contractInstanceContractId)
  (LensFor contractInstanceWallet)
  (LensFor contractInstanceState)
  (LensFor contractInstanceActive)
  = tableLenses

type ContractInstance   = ContractInstanceT Identity
type ContractInstanceId = PrimaryKey ContractInstanceT Identity

instance Table ContractInstanceT where
  data PrimaryKey ContractInstanceT f = ContractInstanceId (Columnar f Text) deriving (Generic, Beamable)
  primaryKey = ContractInstanceId . _contractInstanceId

data Db f = Db
    { _contractInstances :: f (TableEntity ContractInstanceT)
    }
    deriving (Generic, Database be)

db :: DatabaseSettings be Db
db = defaultDbSettings

checkedSqliteDb :: CheckedDatabaseSettings Sqlite Db
checkedSqliteDb = defaultMigratableDbSettings
