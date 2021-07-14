{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Database.Beam.Sqlite.Connection
  ( Sqlite(..), SqliteM(..)
  , sqliteUriSyntax

  , runBeamSqlite, runBeamSqliteDebug

    -- * Emulated @INSERT RETURNING@ support
  , insertReturning, runInsertReturningList
  ) where

import           Prelude hiding (fail)

import           Database.Beam.Backend
import           Database.Beam.Backend.Internal.Compat
import qualified Database.Beam.Backend.SQL.BeamExtensions as Beam
import           Database.Beam.Backend.URI
import           Database.Beam.Migrate.Generics
import           Database.Beam.Migrate.SQL ( BeamMigrateOnlySqlBackend, FieldReturnType(..) )
import qualified Database.Beam.Migrate.SQL as Beam
import           Database.Beam.Migrate.SQL.BeamExtensions
import           Database.Beam.Query ( SqlInsert(..), SqlInsertValues(..)
                                     , HasQBuilder(..), HasSqlEqualityCheck
                                     , HasSqlQuantifiedEqualityCheck
                                     , DataType(..)
                                     , HasSqlInTable(..)
                                     , insert, current_ )
import           Database.Beam.Query.Internal
import           Database.Beam.Query.SQL92
import           Database.Beam.Schema.Tables ( Beamable
                                             , Columnar'(..)
                                             , DatabaseEntity(..)
                                             , DatabaseEntityDescriptor(..)
                                             , TableEntity
                                             , TableField(..)
                                             , allBeamValues
                                             , changeBeamRep )
import           Database.Beam.Sqlite.Syntax

import           Database.SQLite.Simple ( Connection, ToRow(..), FromRow(..)
                                        , Query(..), SQLData(..), field
                                        , execute, execute_
                                        , withStatement, bind, nextRow
                                        , query_, open, close )
import           Database.SQLite.Simple.FromField ( FromField(..), ResultError(..)
                                                  , returnError, fieldData)
import           Database.SQLite.Simple.Internal (RowParser(RP), unRP)
import           Database.SQLite.Simple.Ok (Ok(..))
import           Database.SQLite.Simple.Types (Null)

import           Control.Exception (SomeException(..), bracket_, onException, mask)
import           Control.Monad (forM_)
import           Control.Monad.Fail (MonadFail(..))
import           Control.Monad.Free.Church
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.Identity (Identity)
import           Control.Monad.Reader (ReaderT(..), MonadReader(..), runReaderT)
import           Control.Monad.State.Strict (MonadState(..), StateT(..), runStateT)
import           Control.Monad.Trans (lift)
import           Control.Monad.Writer (tell, execWriter)

import           Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.DList as D
import           Data.Int
import           Data.Maybe (mapMaybe)
import           Data.Proxy (Proxy(..))
import           Data.Scientific (Scientific)
import           Data.String (fromString)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T (decodeUtf8)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TL (decodeUtf8)
import           Data.Time ( LocalTime, UTCTime, Day
                           , ZonedTime, utc, utcToLocalTime )
import           Data.Typeable (cast)
import           Data.Word
import           GHC.TypeLits

import           Network.URI

#ifdef UNIX
import           System.Posix.Process (getProcessID)
#elif defined(WINDOWS)
import           System.Win32.Process (getCurrentProcessId)
#else
#error Need either POSIX or Win32 API for MonadBeamInsertReturning
#endif

import           Text.Read (readMaybe)

-- | The SQLite backend. Used to parameterize 'MonadBeam' and 'FromBackendRow'
-- to provide support for SQLite databases. See the documentation for
-- 'MonadBeam' and the <https://haskell-beam.github.io/beam/ user guide> for more
-- information on how to use this backend.
data Sqlite = Sqlite

instance BeamBackend Sqlite where
  type BackendFromField Sqlite = FromField

instance HasQBuilder Sqlite where
  buildSqlQuery = buildSql92Query' False -- SQLite does not support arbitrarily nesting UNION, INTERSECT, and EXCEPT

instance HasSqlInTable Sqlite where
  inRowValuesE Proxy e es = SqliteExpressionSyntax $ mconcat
    [ parens $ fromSqliteExpression e
    , emit " IN "
    , parens $ emit "VALUES " <> commas (map fromSqliteExpression es)
    ]

instance BeamSqlBackendIsString Sqlite T.Text
instance BeamSqlBackendIsString Sqlite String

instance FromBackendRow Sqlite Bool
instance FromBackendRow Sqlite Double
instance FromBackendRow Sqlite Float
instance FromBackendRow Sqlite Int8
instance FromBackendRow Sqlite Int16
instance FromBackendRow Sqlite Int32
instance FromBackendRow Sqlite Int64
instance FromBackendRow Sqlite Integer
instance FromBackendRow Sqlite Word8
instance FromBackendRow Sqlite Word16
instance FromBackendRow Sqlite Word32
instance FromBackendRow Sqlite Word64
instance FromBackendRow Sqlite BS.ByteString
instance FromBackendRow Sqlite BL.ByteString
instance FromBackendRow Sqlite T.Text
instance FromBackendRow Sqlite TL.Text
instance FromBackendRow Sqlite UTCTime
instance FromBackendRow Sqlite Day
instance FromBackendRow Sqlite Null
instance FromBackendRow Sqlite Char where
  fromBackendRow = do
    t <- fromBackendRow
    case T.uncons t of
      Just (c, _) -> pure c
      _ -> fail "Need string of size one to parse Char"
instance FromBackendRow Sqlite SqlNull where
  fromBackendRow =
    SqlNull <$ (fromBackendRow :: FromBackendRowM Sqlite Null)
instance FromBackendRow Sqlite LocalTime where
  fromBackendRow = utcToLocalTime utc <$> fromBackendRow
instance FromBackendRow Sqlite Scientific where
  fromBackendRow = unSqliteScientific <$> fromBackendRow
instance FromBackendRow Sqlite SqliteScientific

instance TypeError (PreferExplicitSize Int Int32) => FromBackendRow Sqlite Int
instance TypeError (PreferExplicitSize Word Word32) => FromBackendRow Sqlite Word

newtype SqliteScientific = SqliteScientific { unSqliteScientific :: Scientific }
instance FromField SqliteScientific where
  fromField f =
    SqliteScientific <$>
    case fieldData f of
      SQLInteger i -> pure (fromIntegral i)
      SQLFloat d -> pure . fromRational . toRational $ d
      SQLText t -> tryRead (T.unpack t)
      SQLBlob b -> tryRead (BS.unpack b)
      SQLNull -> returnError UnexpectedNull f "null"
    where
      tryRead s =
        case readMaybe s of
          Nothing -> returnError ConversionFailed f $
                     "No conversion to Scientific for '" <> s <> "'"
          Just s'  -> pure s'

instance BeamSqlBackend Sqlite
instance BeamMigrateOnlySqlBackend Sqlite
type instance BeamSqlBackendSyntax Sqlite = SqliteCommandSyntax

data SqliteHasDefault = SqliteHasDefault
instance FieldReturnType 'True 'False Sqlite resTy a =>
         FieldReturnType 'False 'False Sqlite resTy (SqliteHasDefault -> a) where
  field' _ _ nm ty _ collation constraints SqliteHasDefault =
    field' (Proxy @'True) (Proxy @'False) nm ty Nothing collation constraints

instance BeamSqlBackendHasSerial Sqlite where
  genericSerial nm = Beam.field nm (DataType sqliteSerialType) SqliteHasDefault

-- | 'MonadBeam' instance inside whiche SQLite queries are run. See the
-- <https://haskell-beam.github.io/beam/ user guide> for more information
newtype SqliteM a
  = SqliteM
  { runSqliteM :: ReaderT (String -> IO (), Connection) IO a
    -- ^ Run an IO action with access to a SQLite connection and a debug logging
    -- function, called or each query submitted on the connection.
  } deriving (Monad, Functor, Applicative, MonadIO, MonadFail)

newtype BeamSqliteParams = BeamSqliteParams [SQLData]
instance ToRow BeamSqliteParams where
  toRow (BeamSqliteParams x) = x

newtype BeamSqliteRow a = BeamSqliteRow a
instance FromBackendRow Sqlite a => FromRow (BeamSqliteRow a) where
  fromRow = BeamSqliteRow <$> runF fromBackendRow' finish step
      where
        FromBackendRowM fromBackendRow' = fromBackendRow :: FromBackendRowM Sqlite a

        translateErrors :: Maybe Int -> SomeException -> Maybe SomeException
        translateErrors col (SomeException e) =
          case cast e of
            Just (ConversionFailed { errSQLType     = typeString
                                   , errHaskellType = hsString
                                   , errMessage     = msg }) ->
              Just (SomeException (BeamRowReadError col (ColumnTypeMismatch hsString typeString ("conversion failed: " ++ msg))))
            Just (UnexpectedNull {}) ->
              Just (SomeException (BeamRowReadError col ColumnUnexpectedNull))
            Just (Incompatible { errSQLType     = typeString
                               , errHaskellType = hsString
                               , errMessage     = msg }) ->
              Just (SomeException (BeamRowReadError col (ColumnTypeMismatch hsString typeString ("incompatible: " ++ msg))))
            Nothing -> Nothing

        finish = pure

        step :: forall a'. FromBackendRowF Sqlite (RowParser a') -> RowParser a'
        step (ParseOneField next) =
            RP $ ReaderT $ \ro -> StateT $ \st@(col, _) ->
            case runStateT (runReaderT (unRP field) ro) st of
              Ok (x, st') -> runStateT (runReaderT (unRP (next x)) ro) st'
              Errors errs -> Errors (mapMaybe (translateErrors (Just col)) errs)
        step (Alt (FromBackendRowM a) (FromBackendRowM b) next) = do
          RP $ do
            let RP a' = runF a finish step
                RP b' = runF b finish step

            st <- get
            ro <- ask
            case runStateT (runReaderT a' ro) st of
              Ok (ra, st') -> do
                put st'
                unRP (next ra)
              Errors aErrs ->
                case runStateT (runReaderT b' ro) st of
                  Ok (rb, st') -> do
                    put st'
                    unRP (next rb)
                  Errors bErrs ->
                    lift (lift (Errors (aErrs ++ bErrs)))
        step (FailParseWith err) = RP (lift (lift (Errors [SomeException err])))

-- * Equality checks
#define HAS_SQLITE_EQUALITY_CHECK(ty)                       \
  instance HasSqlEqualityCheck Sqlite (ty); \
  instance HasSqlQuantifiedEqualityCheck Sqlite (ty);

HAS_SQLITE_EQUALITY_CHECK(Int8)
HAS_SQLITE_EQUALITY_CHECK(Int16)
HAS_SQLITE_EQUALITY_CHECK(Int32)
HAS_SQLITE_EQUALITY_CHECK(Int64)
HAS_SQLITE_EQUALITY_CHECK(Word8)
HAS_SQLITE_EQUALITY_CHECK(Word16)
HAS_SQLITE_EQUALITY_CHECK(Word32)
HAS_SQLITE_EQUALITY_CHECK(Word64)
HAS_SQLITE_EQUALITY_CHECK(Double)
HAS_SQLITE_EQUALITY_CHECK(Float)
HAS_SQLITE_EQUALITY_CHECK(Bool)
HAS_SQLITE_EQUALITY_CHECK(String)
HAS_SQLITE_EQUALITY_CHECK(T.Text)
HAS_SQLITE_EQUALITY_CHECK(TL.Text)
HAS_SQLITE_EQUALITY_CHECK(BS.ByteString)
HAS_SQLITE_EQUALITY_CHECK(BL.ByteString)
HAS_SQLITE_EQUALITY_CHECK(UTCTime)
HAS_SQLITE_EQUALITY_CHECK(LocalTime)
HAS_SQLITE_EQUALITY_CHECK(ZonedTime)
HAS_SQLITE_EQUALITY_CHECK(Char)
HAS_SQLITE_EQUALITY_CHECK(Integer)
HAS_SQLITE_EQUALITY_CHECK(Scientific)

instance TypeError (PreferExplicitSize Int Int32) => HasSqlEqualityCheck Sqlite Int
instance TypeError (PreferExplicitSize Int Int32) => HasSqlQuantifiedEqualityCheck Sqlite Int
instance TypeError (PreferExplicitSize Word Word32) => HasSqlEqualityCheck Sqlite Word
instance TypeError (PreferExplicitSize Word Word32) => HasSqlQuantifiedEqualityCheck Sqlite Word

class HasDefaultSqlDataType Sqlite a => IsSqliteSerialIntegerType a
instance IsSqliteSerialIntegerType Int32
instance IsSqliteSerialIntegerType Int64
instance TypeError (PreferExplicitSize Int Int32) => IsSqliteSerialIntegerType Int

instance IsSqliteSerialIntegerType a => HasDefaultSqlDataType Sqlite (SqlSerial a) where
  defaultSqlDataType _ _ False = sqliteSerialType
  defaultSqlDataType _ _ True = intType

instance HasDefaultSqlDataType Sqlite BS.ByteString where
  -- TODO we should somehow allow contsraints based on backend
  defaultSqlDataType _ _ _ = sqliteBlobType

instance HasDefaultSqlDataType Sqlite LocalTime where
  defaultSqlDataType _ _ _ = timestampType Nothing False

-- | URI syntax for use with 'withDbConnection'. See documentation for
-- 'BeamURIOpeners' for more information.
sqliteUriSyntax :: c Sqlite Connection SqliteM
                -> BeamURIOpeners c
sqliteUriSyntax =
  mkUriOpener runBeamSqlite "sqlite:"
    (\uri -> do
        let sqliteName = if null (uriPath uri) then ":memory:" else uriPath uri
        hdl <- open sqliteName
        pure (hdl, close hdl))

runBeamSqliteDebug :: (String -> IO ()) -> Connection -> SqliteM a -> IO a
runBeamSqliteDebug debugStmt conn x = runReaderT (runSqliteM x) (debugStmt, conn)

runBeamSqlite :: Connection -> SqliteM a -> IO a
runBeamSqlite = runBeamSqliteDebug (\_ -> pure ())

instance MonadBeam Sqlite SqliteM where
  runNoReturn (SqliteCommandSyntax (SqliteSyntax cmd vals)) =
    SqliteM $ do
      (logger, conn) <- ask
      let cmdString = BL.unpack (toLazyByteString (withPlaceholders cmd))
      liftIO (logger (cmdString ++ ";\n-- With values: " ++ show (D.toList vals)))
      liftIO (execute conn (fromString cmdString) (D.toList vals))
  runNoReturn (SqliteCommandInsert insertStmt_) =
    SqliteM $ do
      (logger, conn) <- ask
      liftIO (runSqliteInsert logger conn insertStmt_)

  runReturningMany (SqliteCommandSyntax (SqliteSyntax cmd vals)) action =
      SqliteM $ do
        (logger, conn) <- ask
        let cmdString = BL.unpack (toLazyByteString (withPlaceholders cmd))
        liftIO $ do
          logger (cmdString ++ ";\n-- With values: " ++ show (D.toList vals))
          withStatement conn (fromString cmdString) $ \stmt ->
            do bind stmt (BeamSqliteParams (D.toList vals))
               let nextRow' = liftIO (nextRow stmt) >>= \x ->
                              case x of
                                Nothing -> pure Nothing
                                Just (BeamSqliteRow row) -> pure row
               runReaderT (runSqliteM (action nextRow')) (logger, conn)
  runReturningMany SqliteCommandInsert {} _ =
      fail . mconcat $
      [ "runReturningMany{Sqlite}: sqlite does not support returning "
      , "rows from an insert, use Database.Beam.Sqlite.insertReturning "
      , "for emulation" ]

instance Beam.MonadBeamInsertReturning Sqlite SqliteM where
  runInsertReturningList = runInsertReturningList

runSqliteInsert :: (String -> IO ()) -> Connection -> SqliteInsertSyntax -> IO ()
runSqliteInsert logger conn (SqliteInsertSyntax tbl fields vs onConflict)
    -- If all expressions are simple expressions (no default), then just

  | SqliteInsertExpressions es <- vs, any (any (== SqliteExpressionDefault)) es =
      forM_ es $ \row -> do
        let (fields', row') = unzip $ filter ((/= SqliteExpressionDefault) . snd) $ zip fields row
            SqliteSyntax cmd vals = formatSqliteInsertOnConflict tbl fields' (SqliteInsertExpressions [ row' ]) onConflict
            cmdString = BL.unpack (toLazyByteString (withPlaceholders cmd))
        logger (cmdString ++ ";\n-- With values: " ++ show (D.toList vals))
        execute conn (fromString cmdString) (D.toList vals)
  | otherwise = do
      let SqliteSyntax cmd vals = formatSqliteInsertOnConflict tbl fields vs onConflict
          cmdString = BL.unpack (toLazyByteString (withPlaceholders cmd))
      logger (cmdString ++ ";\n-- With values: " ++ show (D.toList vals))
      execute conn (fromString cmdString) (D.toList vals)

-- * emulated INSERT returning support

-- | Build a 'SqliteInsertReturning' representing inserting the given values
-- into the given table. Use 'runInsertReturningList'
insertReturning :: Beamable table
                => DatabaseEntity Sqlite db (TableEntity table)
                -> SqlInsertValues Sqlite (table (QExpr Sqlite s))
                -> SqlInsert Sqlite table
insertReturning = insert

-- | Runs a 'SqliteInsertReturning' statement and returns a result for each
-- inserted row.
runInsertReturningList :: (Beamable table, FromBackendRow Sqlite (table Identity))
                       => SqlInsert Sqlite table
                       -> SqliteM [ table Identity ]
runInsertReturningList SqlInsertNoRows = pure []
runInsertReturningList (SqlInsert tblSettings insertStmt_@(SqliteInsertSyntax nm _ _ _)) =
  do (logger, conn) <- SqliteM ask
     SqliteM . liftIO $ do

#ifdef UNIX
       processId <- fromString . show <$> getProcessID
#elif defined(WINDOWS)
       processId <- fromString . show <$> getCurrentProcessId
#else
#error Need either POSIX or Win32 API for MonadBeamInsertReturning
#endif

       let tableNameTxt = T.decodeUtf8 (BL.toStrict (sqliteRenderSyntaxScript (fromSqliteTableName nm)))

           startSavepoint =
             execute_ conn (Query ("SAVEPOINT insert_savepoint_" <> processId))
           rollbackToSavepoint =
             execute_ conn (Query ("ROLLBACK TRANSACTION TO SAVEPOINT insert_savepoint_" <> processId))
           releaseSavepoint =
             execute_ conn (Query ("RELEASE SAVEPOINT insert_savepoint_" <> processId))

           createInsertedValuesTable =
             execute_ conn (Query ("CREATE TEMPORARY TABLE inserted_values_" <> processId <> " AS SELECT * FROM " <> tableNameTxt <> " LIMIT 0"))
           dropInsertedValuesTable =
             execute_ conn (Query ("DROP TABLE inserted_values_" <> processId))

           createInsertTrigger =
             execute_ conn (Query ("CREATE TEMPORARY TRIGGER insert_trigger_" <> processId <> " AFTER INSERT ON " <> tableNameTxt <> " BEGIN " <>
                                   "INSERT INTO inserted_values_" <> processId <> " SELECT * FROM " <> tableNameTxt <> " WHERE ROWID=last_insert_rowid(); END" ))
           dropInsertTrigger =
             execute_ conn (Query ("DROP TRIGGER insert_trigger_" <> processId))


       mask $ \restore -> do
         startSavepoint
         flip onException rollbackToSavepoint . restore $ do
           x <- bracket_ createInsertedValuesTable dropInsertedValuesTable $
                bracket_ createInsertTrigger dropInsertTrigger $ do
                runSqliteInsert logger conn insertStmt_

                let columns = TL.toStrict $ TL.decodeUtf8 $
                              sqliteRenderSyntaxScript $ commas $
                              allBeamValues (\(Columnar' projField) -> quotedIdentifier (_fieldName projField)) $
                              tblSettings

                fmap (\(BeamSqliteRow r) -> r) <$> query_ conn (Query ("SELECT " <> columns <> " FROM inserted_values_" <> processId))
           releaseSavepoint
           return x

instance Beam.BeamHasInsertOnConflict Sqlite where
  newtype SqlConflictTarget Sqlite table = SqliteConflictTarget
    { unSqliteConflictTarget :: table (QExpr Sqlite QInternal) -> SqliteSyntax }
  newtype SqlConflictAction Sqlite table = SqliteConflictAction
    { unSqliteConflictAction :: forall s. table (QField s) -> SqliteSyntax }

  insertOnConflict
    :: forall db table s. Beamable table
    => DatabaseEntity Sqlite db (TableEntity table)
    -> SqlInsertValues Sqlite (table (QExpr Sqlite s))
    -> Beam.SqlConflictTarget Sqlite table
    -> Beam.SqlConflictAction Sqlite table
    -> SqlInsert Sqlite table
  insertOnConflict (DatabaseEntity dt) values target action = case values of
    SqlInsertValuesEmpty -> SqlInsertNoRows
    SqlInsertValues vs -> SqlInsert (dbTableSettings dt) $
      let getFieldName
            :: forall a
            .  Columnar' (TableField table) a
            -> Columnar' (QField QInternal) a
          getFieldName (Columnar' fd) =
            Columnar' $ QField False (dbTableCurrentName dt) $ _fieldName fd
          tableFields = changeBeamRep getFieldName $ dbTableSettings dt
          tellFieldName _ _ f = tell [f] >> pure f
          fieldNames = execWriter $
            project' (Proxy @AnyType) (Proxy @((), T.Text)) tellFieldName tableFields
          currentField
            :: forall a
            .  Columnar' (QField QInternal) a
            -> Columnar' (QExpr Sqlite QInternal) a
          currentField (Columnar' f) = Columnar' $ current_ f
          tableCurrent = changeBeamRep currentField tableFields
      in SqliteInsertSyntax (tableNameFromEntity dt) fieldNames vs $ Just $
           SqliteOnConflictSyntax $ mconcat
             [ emit "ON CONFLICT "
             , unSqliteConflictTarget target tableCurrent
             , emit " DO "
             , unSqliteConflictAction action tableFields
             ]

  anyConflict = SqliteConflictTarget $ const mempty
  conflictingFields makeProjection = SqliteConflictTarget $ \table ->
    parens $ commas $ map fromSqliteExpression $
      project (Proxy @Sqlite) (makeProjection table) "t"
  conflictingFieldsWhere makeProjection makeWhere =
    SqliteConflictTarget $ \table -> mconcat
      [ unSqliteConflictTarget (Beam.conflictingFields makeProjection) table
      , emit " WHERE "
      , let QExpr mkE = makeWhere table
        in fromSqliteExpression $ mkE "t"
      ]

  onConflictDoNothing = SqliteConflictAction $ const $ emit "NOTHING"
  onConflictUpdateSet makeAssignments = SqliteConflictAction $ \table -> mconcat
    [ emit "UPDATE SET "
    , let QAssignment assignments = makeAssignments table $ excluded table
          emitAssignment (fieldName, expr) = mconcat
            [ fromSqliteFieldNameSyntax fieldName
            , emit " = "
            , fromSqliteExpression expr
            ]
      in commas $ map emitAssignment assignments
    ]
  onConflictUpdateSetWhere makeAssignments makeWhere =
    SqliteConflictAction $ \table -> mconcat
      [ unSqliteConflictAction (Beam.onConflictUpdateSet makeAssignments) table
      , emit " WHERE "
      , let QExpr mkE = makeWhere table $ excluded table
        in fromSqliteExpression $ mkE "t"
      ]

excluded
  :: forall table s
  .  Beamable table
  => table (QField s)
  -> table (QExpr Sqlite s)
excluded table = changeBeamRep excludedField table
  where excludedField (Columnar' (QField _ _ name)) =
          Columnar' $ QExpr $ const $ fieldE $ qualifiedField "excluded" name
