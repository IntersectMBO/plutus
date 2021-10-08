{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}

module Control.Monad.Freer.Extras.Beam where

import           Cardano.BM.Data.Tracer                   (ToObject (..))
import           Cardano.BM.Trace                         (Trace, logDebug)
import           Control.Concurrent                       (threadDelay)
import           Control.Exception                        (try)
import           Control.Monad.Freer                      (Eff, LastMember, Member, type (~>))
import           Control.Monad.Freer.Error                (Error, throwError)
import           Control.Monad.Freer.Reader               (Reader, ask)
import           Control.Monad.Freer.TH                   (makeEffect)
import           Data.Aeson                               (FromJSON, ToJSON)
import           Data.Foldable                            (traverse_)
import           Data.Text                                (Text)
import qualified Data.Text                                as Text
import           Database.Beam                            (Beamable, DatabaseEntity, FromBackendRow, Identity,
                                                           MonadIO (liftIO), SqlDelete, SqlInsert, SqlSelect, SqlUpdate,
                                                           TableEntity, insertValues, runDelete, runInsert,
                                                           runSelectReturningList, runSelectReturningOne, runUpdate)
import           Database.Beam.Backend.SQL                (BeamSqlBackendCanSerialize)
import           Database.Beam.Backend.SQL.BeamExtensions (BeamHasInsertOnConflict (anyConflict, insertOnConflict, onConflictDoNothing))
import           Database.Beam.Schema.Tables              (FieldsFulfillConstraint)
import           Database.Beam.Sqlite                     (Sqlite, SqliteM, runBeamSqliteDebug)
import qualified Database.SQLite.Simple                   as Sqlite
import           GHC.Generics                             (Generic)
import           Prettyprinter                            (Pretty (..), colon, (<+>))

type BeamableSqlite table = (Beamable table, FieldsFulfillConstraint (BeamSqlBackendCanSerialize Sqlite) table)

data BeamError =
  SqlError Text
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON, ToObject)

instance Pretty BeamError where
  pretty = \case
    SqlError s -> "SqlError (via Beam)" <> colon <+> pretty s

data BeamLog =
  SqlLog String
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON, ToObject)

instance Pretty BeamLog where
  pretty = \case
    SqlLog s -> "SqlLog" <> colon <+> pretty s

data BeamEffect r where
  -- Workaround for "too many SQL variables" sqlite error. Provide a
  -- batch size so that we avoid the error. The maximum is 999.
  AddRowsInBatches
    :: BeamableSqlite table
    => Int
    -> DatabaseEntity Sqlite db (TableEntity table)
    -> [table Identity]
    -> BeamEffect ()

  AddRows
    :: BeamableSqlite table
    => SqlInsert Sqlite table
    -> BeamEffect ()

  UpdateRows
    :: Beamable table
    => SqlUpdate Sqlite table
    -> BeamEffect ()

  DeleteRows
    :: Beamable table
    => SqlDelete Sqlite table
    -> BeamEffect ()

  SelectList
    :: FromBackendRow Sqlite a
    => SqlSelect Sqlite a
    -> BeamEffect [a]

  SelectOne
    :: FromBackendRow Sqlite a
    => SqlSelect Sqlite a
    -> BeamEffect (Maybe a)

  Combined
    :: [BeamEffect ()]
    -> BeamEffect ()

handleBeam ::
  forall effs.
  ( LastMember IO effs
  , Member (Error BeamError) effs
  , Member (Reader Sqlite.Connection) effs
  )
  => Trace IO BeamLog
  -> BeamEffect
  ~> Eff effs
handleBeam trace eff = runBeam trace $ execute eff
  where
    execute :: BeamEffect ~> SqliteM
    execute = \case
        AddRowsInBatches _ _ [] -> pure ()
        AddRowsInBatches n table (splitAt n -> (batch, rest)) -> do
            runInsert $ insertOnConflict table (insertValues batch) anyConflict onConflictDoNothing
            execute $ AddRowsInBatches n table rest
        AddRows    q    -> runInsert q
        UpdateRows q    -> runUpdate q
        DeleteRows q    -> runDelete q
        SelectList q    -> runSelectReturningList q
        SelectOne  q    -> runSelectReturningOne  q
        Combined   effs -> traverse_ execute effs

runBeam ::
  forall effs.
  ( LastMember IO effs
  , Member (Error BeamError) effs
  , Member (Reader Sqlite.Connection) effs
  )
  => Trace IO BeamLog
  -> SqliteM
  ~> Eff effs
runBeam trace action = do
  conn <- ask @Sqlite.Connection
  loop conn ( 5 :: Int )
  where
    loop conn retries = do
      let traceSql = logDebug trace . SqlLog
      resultEither <- liftIO $ try $ Sqlite.withTransaction conn $ runBeamSqliteDebug traceSql conn action
      case resultEither of
          -- 'Database.SQLite.Simple.ErrorError' corresponds to an SQL error or
          -- missing database. When this exception is raised, we suppose it's
          -- because the another transaction was already running.
          Left (Sqlite.SQLError Sqlite.ErrorError _ _) | retries > 0 -> do
              liftIO $ threadDelay 100_000
              loop conn (retries - 1)
          -- We handle and rethrow errors other than
          -- 'Database.SQLite.Simple.ErrorError'.
          Left e -> do
              throwError $ SqlError $ Text.pack $ show e
          Right v -> return v

makeEffect ''BeamEffect
