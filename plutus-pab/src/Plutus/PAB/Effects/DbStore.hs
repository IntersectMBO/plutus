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

A beam-specific effect for writing to a beam database. Here we explicitly construct the
database schema for the effects which we wish to store:

- 'Pluts.PAB.Effects.Contract.ContractStore' effect
- 'Pluts.PAB.Effects.Contract.ContractDefinitionStore' effect

In particular this is specialised to 'Sqlite'; but it could be refactored to
work over a more general type, or changed to Postgres.

The schema we've opted for at present is a very simple one, with no ability to
track changes over time.

-}

module Plutus.PAB.Effects.DbStore where
import           Cardano.BM.Trace                (Trace, logDebug)
import           Control.Exception               (try)
import           Control.Monad.Freer             (Eff, LastMember, Member, type (~>))
import           Control.Monad.Freer.Error       (Error, throwError)
import           Control.Monad.Freer.Reader      (Reader, ask)
import           Control.Monad.Freer.TH          (makeEffect)
import           Data.Text                       (Text)
import qualified Data.Text                       as Text
import           Database.Beam
import           Database.Beam.Backend.SQL
import           Database.Beam.Migrate
import           Database.Beam.Schema.Tables
import           Database.Beam.Sqlite            (Sqlite, SqliteM, runBeamSqliteDebug)
import qualified Database.SQLite.Simple          as Sqlite
import           Plutus.PAB.Monitoring.PABLogMsg (PABLogMsg (..), PABMultiAgentMsg (..))
import           Plutus.PAB.Types                (PABError (MigrationNotDoneError, OtherError))

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

-- | Effect for managing a beam-based database.
data DbStoreEffect r where
  -- | Insert a row into a table.
  AddRow
    ::
    ( Beamable table
    , FieldsFulfillConstraint (BeamSqlBackendCanSerialize Sqlite) table
    )
    => DatabaseEntity Sqlite Db (TableEntity table)
    -> table Identity
    -> DbStoreEffect ()

  UpdateRow
    ::
    ( Beamable table
    )
    => SqlUpdate Sqlite table
    -> DbStoreEffect ()

  SelectList
    ::
    ( Beamable table
    , FromBackendRow Sqlite (table Identity)
    )
    => SqlSelect Sqlite (table Identity)
    -> DbStoreEffect [table Identity]

  SelectOne
    ::
    ( Beamable table
    , FromBackendRow Sqlite (table Identity)
    )
    => SqlSelect Sqlite (table Identity)
    -> DbStoreEffect (Maybe (table Identity))

handleDbStore ::
  forall a effs.
  ( Member (Reader Sqlite.Connection) effs
  , Member (Error PABError) effs
  , LastMember IO effs
  )
  => Trace IO (PABLogMsg a)
  -> DbStoreEffect
  ~> Eff effs
handleDbStore trace eff = do
  case eff of
    AddRow table record ->
        runBeamPABEff trace $ runInsert $ insert table (insertValues [record])

    SelectList q -> runBeamPABEff trace $ runSelectReturningList q

    SelectOne q -> runBeamPABEff trace $ runSelectReturningOne q

    UpdateRow q -> runBeamPABEff trace $ runUpdate q

-- | Same as 'Database.Beam.Sqlite.runBeamSqliteDebug', but exceptions are
-- handled and converted to the 'PABError' datatype.
--
-- This is done in order to catch an error that occurs in the case where the
-- 'migrate' was not executed before running the PAB webserver.
runBeamPABEff ::
  forall a b effs.
  ( Member (Reader Sqlite.Connection) effs
  , Member (Error PABError) effs
  , LastMember IO effs
  )
  => Trace IO (PABLogMsg a)
  -> SqliteM b
  -> Eff effs b
runBeamPABEff trace action = do
    connection <- ask @Sqlite.Connection
    let traceSql = logDebug trace . SMultiAgent . SqlLog
    resultEither <- liftIO $ try $ runBeamSqliteDebug traceSql connection action
    case resultEither of
        -- 'Database.SQLite.Simple.ErrorError' corresponds to an SQL error or
        -- missing database. When this exception is raised, we suppose it's
        -- because the 'migrate' command was not executed before running the
        -- PAB webserver. We throw back a 'PABError'.
        Left e@(Sqlite.SQLError Sqlite.ErrorError _ _) -> do
            throwError $ MigrationNotDoneError $ Text.pack $ show e
        -- We handle and rethrow errors other than
        -- 'Database.SQLite.Simple.ErrorError'.
        Left e -> do
            throwError $ OtherError $ Text.pack $ show e
        Right v -> return v

makeEffect ''DbStoreEffect
