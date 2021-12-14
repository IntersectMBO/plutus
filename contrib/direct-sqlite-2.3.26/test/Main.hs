import StrictEq

import Database.SQLite3
import qualified Database.SQLite3.Direct as Direct

import Control.Concurrent
import Control.Exception
import Control.Monad        (forM_, liftM3, when)
import Data.Text            (Text)
import Data.Text.Encoding.Error (UnicodeException(..))
import Data.Typeable
import Data.Monoid
import System.Directory     ()
import System.Exit          (exitFailure)
import System.IO
import System.IO.Error      (isUserError)
import System.IO.Temp       (withTempFile)
import System.Timeout       (timeout)
import Test.HUnit

import qualified Data.ByteString        as B
import qualified Data.ByteString.Char8  as B8
import qualified Data.Text              as T
import qualified Data.Text.Encoding     as T

data TestEnv =
  TestEnv {
    conn :: Database
    -- ^ Database shared by all the tests
  , withConn :: forall a. (Database -> IO a) -> IO a
    -- ^ Bracket for spawning an additional connection.
    --   This connection will be isolated from others.
  , withConnShared :: forall a. (Database -> IO a) -> IO a
    -- ^ Like 'withConn', but every invocation shares the same database.
  }

regressionTests :: [TestEnv -> Test]
regressionTests =
    [ TestLabel "Exec"          . testExec
    , TestLabel "ExecCallback"  . testExecCallback
    , TestLabel "Simple"        . testSimplest
    , TestLabel "Prepare"       . testPrepare
    , TestLabel "CloseBusy"     . testCloseBusy
    , TestLabel "Params"        . testBind
    , TestLabel "Params"        . testBindParamCounts
    , TestLabel "Params"        . testBindParamName
    , TestLabel "Params"        . testBindErrorValidation
    , TestLabel "Params"        . testNamedBindParams
    , TestLabel "Columns"       . testColumns
    , TestLabel "TypedColumns"  . testTypedColumns
    , TestLabel "ColumnName"    . testColumnName
    , TestLabel "Errors"        . testErrors
    , TestLabel "Integrity"     . testIntegrity
    , TestLabel "DecodeError"   . testDecodeError
    , TestLabel "ResultStats"   . testResultStats
    , TestLabel "GetAutoCommit" . testGetAutoCommit
    , TestLabel "Debug"         . testStatementSql
    , TestLabel "Debug"         . testTracing
    , TestLabel "CustomFunc"    . testCustomFunction
    , TestLabel "CustomFuncErr" . testCustomFunctionError
    , TestLabel "CustomAggr"    . testCustomAggragate
    , TestLabel "CustomColl"    . testCustomCollation
    , TestLabel "IncrBlobIO"    . testIncrementalBlobIO
    ] ++
    (if rtsSupportsBoundThreads then
    [ TestLabel "Interrupt"     . testInterrupt
    ] else [])

featureTests :: [TestEnv -> Test]
featureTests =
    [ TestLabel "MultiRowInsert" . testMultiRowInsert
    ]

assertFail :: IO a -> Assertion
assertFail action =
  shouldFail action >>= assertBool "assertFail"

-- | Return 'True' if the IO action throws a 'userError',
-- which happens when 'fail' is used.
shouldFail :: IO a -> IO Bool
shouldFail action = do
  r <- try action
  case r of
    Left e  -> return $ isUserError e
    Right _ -> return False

withStmt :: Database -> Text -> (Statement -> IO a) -> IO a
withStmt conn sql = bracket (prepare conn sql) finalize

testExec :: TestEnv -> Test
testExec TestEnv{..} = TestCase $ do
  exec conn ""
  exec conn "     "
  exec conn ";"
  exec conn " ; ; ; ; ; "
  exec conn "--"
  Left SQLError{sqlError = ErrorError} <- try $ exec conn "/*"
    -- sqlite3_exec does not allow "/*" to be terminated by end of input,
    -- but <https://www.sqlite.org/lang_comment.html> says it's fine.
  exec conn ";--\n;/**/"
  withConn $ \conn -> do
    -- Make sure all the statements passed to exec are executed.
    -- Test a little value conversion while we're at it.
    exec conn "CREATE TABLE foo (n FLOAT, t TEXT); \
              \INSERT INTO foo VALUES (3.5, null); \
              \INSERT INTO foo VALUES (null, 'Ự₦ⓘ₡ợ₫ḝ'); \
              \INSERT INTO foo VALUES (null, ''); \
              \INSERT INTO foo VALUES (null, 'null'); \
              \INSERT INTO foo VALUES (null, null)"
    withStmt conn ("SELECT * FROM foo") $ \stmt -> do
      Row <- step stmt
      [SQLFloat 3.5, SQLNull]       <- columns stmt
      Row <- step stmt
      [SQLNull, SQLText "Ự₦ⓘ₡ợ₫ḝ"]  <- columns stmt
      Row <- step stmt
      [SQLNull, SQLText ""]         <- columns stmt
      Row <- step stmt
      [SQLNull, SQLText "null"]     <- columns stmt
      Row <- step stmt
      [SQLNull, SQLNull]            <- columns stmt
      Done <- step stmt
      return ()

data Ex = Ex
    deriving (Show, Typeable)

instance Exception Ex

testExecCallback :: TestEnv -> Test
testExecCallback TestEnv{..} = TestCase $
  withConn $ \conn -> do
    chan <- newChan
    let exec' sql = execWithCallback conn sql $ \c n v -> writeChan chan (c, n, v)
    exec' "CREATE TABLE foo (a INT, b TEXT); \
          \INSERT INTO foo VALUES (1, 'a'); \
          \INSERT INTO foo VALUES (2, 'b'); \
          \INSERT INTO foo VALUES (3, null); \
          \INSERT INTO foo VALUES (null, 'd'); "

    exec' "SELECT 1, 2, 3"
    (3, ["1","2","3"], [Just "1", Just "2", Just "3"]) <- readChan chan

    exec' "SELECT null"
    (1, ["null"], [Nothing]) <- readChan chan

    exec' "SELECT * FROM foo"
    (2, ["a","b"], [Just "1", Just "a"]) <- readChan chan
    (2, ["a","b"], [Just "2", Just "b"]) <- readChan chan
    (2, ["a","b"], [Just "3", Nothing ]) <- readChan chan
    (2, ["a","b"], [Nothing,  Just "d"]) <- readChan chan

    exec' "SELECT * FROM foo WHERE a < 0; SELECT 123"
    (1, ["123"], [Just "123"]) <- readChan chan

    exec' "SELECT rowid, f.a, f.b, a || b FROM foo AS f"
    (4, ["rowid", "a", "b", "a || b"], [Just "1", Just "1", Just "a", Just "1a"]) <- readChan chan
    (4, ["rowid", "a", "b", "a || b"], [Just "2", Just "2", Just "b", Just "2b"]) <- readChan chan
    (4, ["rowid", "a", "b", "a || b"], [Just "3", Just "3", Nothing , Nothing  ]) <- readChan chan
    (4, ["rowid", "a", "b", "a || b"], [Just "4", Nothing , Just "d", Nothing  ]) <- readChan chan

    Left Ex <- try $ execWithCallback conn "SELECT 1" $ \_ _ _ -> throwIO Ex

    return ()


testTracing :: TestEnv -> Test
testTracing TestEnv{..} = TestCase $
  withConn $ \conn -> do
    chan <- newChan
    let logger m = writeChan chan m
    Direct.setTrace conn (Just logger)
    withStmt conn "SELECT null" $ \stmt -> do
      Row <- step stmt
      res <- columns stmt
      Done <- step stmt
      assertEqual "tracing" [SQLNull] res
      Direct.Utf8 msg <- readChan chan
      assertEqual "tracing" "SELECT null" msg
    withStmt conn "SELECT 1+?" $ \stmt -> do
      bind stmt [SQLInteger 2]
      Row <- step stmt
      Done <- step stmt
      reset stmt
      bind stmt [SQLInteger 3]
      Row <- step stmt
      Done <- step stmt
      Direct.Utf8 msg <- readChan chan
      assertEqual "tracing" "SELECT 1+2" msg
      Direct.Utf8 msg <- readChan chan
      assertEqual "tracing" "SELECT 1+3" msg
      -- Check that disabling works too
      Direct.setTrace conn Nothing
      reset stmt
      bind stmt [SQLInteger 3]
      Row <- step stmt
      Done <- step stmt
      writeChan chan (Direct.Utf8 "empty")
      Direct.Utf8 msg <- readChan chan
      assertEqual "tracing" "empty" msg


-- Simplest SELECT
testSimplest :: TestEnv -> Test
testSimplest TestEnv{..} = TestCase $ do
  stmt <- prepare conn "SELECT 1+1"
  Row <- step stmt
  res <- column stmt 0
  Done <- step stmt
  finalize stmt
  assertEqual "1+1" (SQLInteger 2) res

testPrepare :: TestEnv -> Test
testPrepare TestEnv{..} = TestCase $ do
  True <- shouldFail $ prepare conn ""
  True <- shouldFail $ prepare conn ";"
  withConn $ \conn -> do
    withStmt conn
             "CREATE TABLE foo (a INT, b INT); \
             \INSERT INTO foo VALUES (1, 2); \
             \INSERT INTO foo VALUES (3, 4)"
             $ \stmt -> do
      Done <- step stmt
      return ()
    withStmt conn
             "BEGIN; INSERT INTO foo VALUES (5, 6); COMMIT"
             $ \stmt -> do
      Done <- step stmt
      return ()
    withStmt conn
             "SELECT * FROM foo"
             $ \stmt -> do
      Done <- step stmt -- No row was inserted, because only the CREATE TABLE
                        -- statement was run.  The rest was ignored.
      return ()
    Left SQLError{sqlError = ErrorError} <- try $ exec conn "BEGIN"
      -- We're in a transaction already, so this fails.
    exec conn "COMMIT"
  return ()

testCloseBusy :: TestEnv -> Test
testCloseBusy _ = TestCase $ do
  conn <- open ":memory:"
  stmt <- prepare conn "SELECT 1"
  Left SQLError{sqlError = ErrorBusy} <- try $ close conn
  finalize stmt
  close conn

testBind :: TestEnv -> Test
testBind TestEnv{..} = TestCase $ do
  bracket (prepare conn "SELECT ?") finalize testBind1
  bracket (prepare conn "SELECT ?+?") finalize testBind2
  bracket (prepare conn "SELECT ?,?") finalize testBind3
  where
    testBind1 stmt = do
      let params =  [SQLInteger 3]
      bind stmt params
      Row <- step stmt
      res <- columns stmt
      Done <- step stmt
      assertEqual "single param" params res

    testBind2 stmt = do
      let params =  [SQLInteger 1, SQLInteger 1]
      bind stmt params
      Row <- step stmt
      res <- columns stmt
      Done <- step stmt
      assertEqual "two params param" [SQLInteger 2] res

    testBind3 stmt = do
      let len = 7
          bs = B.replicate len 0
      bindBlob stmt 1 bs
      bindZeroBlob stmt 2 len
      Row <- step stmt
      res <- columns stmt
      Done <- step stmt
      assertEqual "blob vs. zeroblob" [SQLBlob bs, SQLBlob bs] res

-- Test bindParameterCount
testBindParamCounts :: TestEnv -> Test
testBindParamCounts TestEnv{..} = TestCase $ do
  testCase "single $a"                  "SELECT $a"                     1
  testCase "3 unique ?NNNs"             "SELECT (?1+?1+?1+?2+?3)"       3
  testCase "3 positional"               "SELECT (?+?+?)"                3
  testCase "5 params, 2 gaps"           "SELECT ?3, ?5, ?1"             5
  testCase "6 params, gaps & auto"      "SELECT ?3, ?5, ?1, ?"          6
  testCase "8 params, auto & overlap"   "SELECT ?, ?5, ?, ?2, ?, ?6, ?" 8
    -- 8 because ? grabs an index one greater than the highest index of all
    -- previous parameters, not just the most recent index.
  testCase "0 placeholders"             "SELECT 1"                      0
  where
    testCase label query expected =
        bracket (prepare conn query) finalize bindParameterCount
            >>= assertEqual label expected

-- Test bindParameterName
testBindParamName :: TestEnv -> Test
testBindParamName TestEnv{..} = TestCase $ do
  bracket (prepare conn "SELECT :v + :v2") finalize (testNames [Just ":v", Just ":v2"])
  bracket (prepare conn "SELECT ?1 + ?1") finalize (testNames [Just "?1"])
  bracket (prepare conn "SELECT ?1 + ?2") finalize (testNames [Just "?1", Just "?2"])
  bracket (prepare conn "SELECT ? + ?") finalize (testNames [Nothing, Nothing])
  bracket (prepare conn "SELECT $1 + $2") finalize (testNames [Just "$1", Just "$2"])
  where
    testNames names stmt = do
      count <- bindParameterCount stmt
      assertEqual "count match" count (fromIntegral $ length names)
      mapM_ (\(ndx,expecting) -> do
                name <- bindParameterName stmt ndx
                assertEqual "name match" expecting name) $ zip [1..] names

testBindErrorValidation :: TestEnv -> Test
testBindErrorValidation TestEnv{..} = TestCase $ do
  bracket (prepare conn "SELECT ?") finalize (assertFail . testException1)
  bracket (prepare conn "SELECT ?") finalize (assertFail . testException2)
  where
    -- Invalid use, one param in q string, none given
    testException1 stmt = bind stmt []
    -- Invalid use, one param in q string, 2 given
    testException2 stmt = bind stmt [SQLInteger 1, SQLInteger 2]

testNamedBindParams :: TestEnv -> Test
testNamedBindParams TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    withStmt conn "SELECT :foo / :bar" $ \stmt -> do
      -- Test that we get something back for known names
      Just fooIdx <- Direct.bindParameterIndex stmt ":foo"
      Just barIdx <- Direct.bindParameterIndex stmt ":bar"
      -- Test that we get Nothing back for unknown names
      Nothing <- Direct.bindParameterIndex stmt "intentionally_undefined"
      Right () <- Direct.bindInt64 stmt fooIdx 4
      Right () <- Direct.bindInt64 stmt barIdx 2
      Row <- step stmt
      1 <- columnCount stmt
      [SQLInteger 2] <- columns stmt
      Done <- step stmt
      return ()
    withStmt conn "SELECT @n1+@n2" $ \stmt -> do
      -- Test that we get something back for known names
      Just _n1 <- Direct.bindParameterIndex stmt "@n1"
      Just _n2 <- Direct.bindParameterIndex stmt "@n2"
      -- Here's where things get confusing..  You can't mix different
      -- types of :/$/@ parameter conventions.
      Nothing <- Direct.bindParameterIndex stmt ":n1"
      Nothing <- Direct.bindParameterIndex stmt ":n2"
      return ()
    withStmt conn "SELECT :foo / :bar,:t" $ \stmt -> do
      bindNamed stmt [(":t", SQLText "txt"), (":foo", SQLInteger 6), (":bar", SQLInteger 2)]
      Row <- step stmt
      2 <- columnCount stmt
      [SQLInteger 3, SQLText "txt"] <- columns stmt
      Done <- step stmt
      return ()

testColumns :: TestEnv -> Test
testColumns TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    withStmt conn "CREATE TABLE foo (a INT)" command
    withStmt conn "SELECT * FROM foo" $ \stmt -> do
      1 <- columnCount stmt
      exec conn "ALTER TABLE foo ADD COLUMN b INT"
      Done <- step stmt
      2 <- columnCount stmt
      return ()
    withStmt conn "SELECT * FROM foo" $ \stmt -> do
      2 <- columnCount stmt
      Done <- step stmt
      2 <- columnCount stmt
      return ()
    withStmt conn "INSERT INTO foo VALUES (1, 2)" command
    withStmt conn "SELECT * FROM foo" $ \stmt -> do
      2 <- columnCount stmt
      Row <- step stmt
      2 <- columnCount stmt
      [SQLInteger 1, SQLInteger 2] <- columns stmt
      Done <- step stmt
      2 <- columnCount stmt
      return ()
    withStmt conn "INSERT INTO foo VALUES (3, 4)" command
    withStmt conn "INSERT INTO foo VALUES (5, 6)" command
    withStmt conn "SELECT * FROM foo" $ \stmt -> do
      2 <- columnCount stmt
      exec conn "ALTER TABLE foo ADD COLUMN c INT"
      Row <- step stmt
      3 <- columnCount stmt
      [SQLInteger 1, SQLInteger 2, SQLNull] <- columns stmt
      exec conn "ALTER TABLE foo ADD COLUMN d INT NOT NULL DEFAULT 42"
        -- ignored by this prepared statement, now that it has stepped.
      Row <- step stmt
      3 <- columnCount stmt
      [SQLInteger 3, SQLInteger 4, SQLNull] <- columns stmt
      Row <- step stmt
      3 <- columnCount stmt
      [SQLInteger 5, SQLInteger 6, SQLNull] <- columns stmt
      Done <- step stmt
      3 <- columnCount stmt
      reset stmt
      3 <- columnCount stmt -- The prepared statement *still* doesn't know
                            -- about the new column.
      Row <- step stmt
      4 <- columnCount stmt -- That's better.
      [SQLInteger 1, SQLInteger 2, SQLNull, SQLInteger 42] <- columns stmt
      return ()
  where
    command stmt = do
      0 <- columnCount stmt
      Done <- step stmt
      0 <- columnCount stmt
      return ()

testTypedColumns :: TestEnv -> Test
testTypedColumns TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    withStmt conn "CREATE TABLE foo (a INT, b INT)" command
    withStmt conn "INSERT INTO foo VALUES (1, 2)" command
    withStmt conn "INSERT INTO foo VALUES (3, 4)" command
    withStmt conn "SELECT * FROM foo" $ \stmt -> do
      Row <- step stmt
      2 <- columnCount stmt
      [SQLInteger 1, SQLInteger 2] <- typedColumns stmt [Nothing, Nothing]
      Row <- step stmt
      2 <- columnCount stmt
      [SQLInteger 3, SQLInteger 4] <- typedColumns stmt [Just IntegerColumn, Just IntegerColumn]
      Done <- step stmt
      2 <- columnCount stmt
      return ()
    withStmt conn "SELECT * FROM foo" $ \stmt -> do
      Row <- step stmt
      2 <- columnCount stmt
      [SQLText "1", SQLText "2"] <- typedColumns stmt [Just TextColumn, Just TextColumn]
      Row <- step stmt
      2 <- columnCount stmt
      [SQLFloat 3.0, SQLFloat 4.0] <- typedColumns stmt [Just FloatColumn, Just FloatColumn]
      Done <- step stmt
      2 <- columnCount stmt
      return ()
  where
    command stmt = do
      0 <- columnCount stmt
      Done <- step stmt
      0 <- columnCount stmt
      return ()

testColumnName :: TestEnv -> Test
testColumnName TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    exec conn "CREATE TABLE foo (id INTEGER PRIMARY KEY, abc TEXT, \"123\" REAL, über INT)"
    exec conn "INSERT INTO foo (abc, \"123\", über) VALUES ('hello', 3.14, 456)"

    withStmt conn "SELECT id AS id, abc AS x, \"123\" AS y, über AS ü FROM foo"
      $ \stmt -> do
      let checkNames = do
              4 <- columnCount stmt
              Nothing   <- columnName stmt (-1)
              Just "id" <- columnName stmt 0
              Just "x"  <- columnName stmt 1
              Just "y"  <- columnName stmt 2
              Just "ü"  <- columnName stmt 3
              Nothing   <- columnName stmt 4
              Nothing   <- columnName stmt minBound
              Nothing   <- columnName stmt maxBound
              return ()
      checkNames
      Row <- step stmt
      checkNames
      [SQLInteger 1, SQLText "hello", SQLFloat 3.14, SQLInteger 456] <- columns stmt
      Done <- step stmt
      checkNames

    -- Column names without AS clauses may change in future versions of SQLite.
    -- This test will fail if they do.
    withStmt conn "SELECT * FROM foo" $ \stmt -> do
      4 <- columnCount stmt
      Nothing     <- columnName stmt (-1)
      Just "id"   <- columnName stmt 0
      Just "abc"  <- columnName stmt 1
      Just "123"  <- columnName stmt 2
      Just "über" <- columnName stmt 3
      Nothing     <- columnName stmt 4
      Nothing     <- columnName stmt minBound
      Nothing     <- columnName stmt maxBound
      return ()

-- Testing for specific error codes:
--
--  * ErrorConstraint
--
--  * ErrorRange
--
--  * ErrorLocked

--  * ErrorBusy
testErrors :: TestEnv -> Test
testErrors TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    exec conn "CREATE TABLE foo (n INT UNIQUE)"
    exec conn "INSERT INTO foo VALUES (3)"
    expectError ErrorConstraint $
      exec conn "INSERT INTO foo VALUES (3)"

    -- Multiple NULLs are allowed when there's a UNIQUE constraint
    exec conn "INSERT INTO foo VALUES (null)"
    exec conn "INSERT INTO foo VALUES (null)"

    exec conn "CREATE TABLE bar (n INT NOT NULL)"
    expectError ErrorConstraint $
      exec conn "INSERT INTO bar VALUES (null)"

    withStmt conn "SELECT ?" $ \stmt -> do
      forM_ [-1, 0, 2] $ \i -> do
        expectError ErrorRange $ bindSQLData stmt i $ SQLInteger 42
        expectError ErrorRange $ bindSQLData stmt i SQLNull
      bindSQLData stmt 1 $ SQLInteger 42
      Row <- step stmt

      -- If column index is out of range, it returns SQLNull.
      -- This may or may not be the desired behavior, but at least we know.
      SQLNull <- column stmt (-1)
      SQLNull <- column stmt 1

      SQLInteger 42 <- column stmt 0
      return ()

    withStmt conn "SELECT 1" $ \stmt -> do
      forM_ [-1, 0, 1, 2] $ \i -> do
        expectError ErrorRange $ bindSQLData stmt i $ SQLInteger 42
        expectError ErrorRange $ bindSQLData stmt i SQLNull
      bind stmt []  -- This should succeed.  Don't whine that there aren't any
                    -- parameters to bind!
      Row <- step stmt
      SQLInteger 1 <- column stmt 0
      return ()

    withStmt conn "SELECT :bar" $ \stmt -> do
      shouldFail $ bindNamed stmt [(":missing", SQLInteger 42)]
      bindNamed stmt [(":bar", SQLInteger 1)]
      Row <- step stmt
      SQLInteger 1 <- column stmt 0
      return ()

    withStmt conn "SELECT ?5" $ \stmt -> do
      forM_ [-1, 0, 6, 7] $ \i -> do
        expectError ErrorRange $ bindSQLData stmt i $ SQLInteger 42
        expectError ErrorRange $ bindSQLData stmt i SQLNull
      bind stmt $ map SQLInteger [1..5]
        -- This succeeds, even though 1..4 aren't used.
      Row <- step stmt
      [SQLInteger 5] <- columns stmt
      return ()

  -- Need to access the database with multiple connections.
  -- "BEGIN; ROLLBACK" causes running statements in the same connection to
  -- throw SQLITE_ABORT.
  withConnShared $ \conn -> do
    foo123456 conn
    withStmt conn "SELECT * FROM foo" $ \stmt -> do
      -- "DROP TABLE foo" should succeed, since the statement
      -- isn't running yet.
      exec conn "DROP TABLE foo"
      foo123456 conn

      Row <- step stmt
      2 <- columnCount stmt
      [SQLInteger 1, SQLInteger 2] <- columns stmt

      -- "DROP TABLE foo" should fail, now that the statement is running.
      expectError ErrorLocked $ exec conn "DROP TABLE foo"
      withConnShared $ \conn -> do
        expectError ErrorBusy $ exec conn "DROP TABLE foo"

        -- Apparently, we can pretend to drop the table, but we get ErrorBusy
        -- if we try to actually COMMIT it.
        exec conn "BEGIN; DROP TABLE foo"
        expectError ErrorBusy $ exec conn "COMMIT"

        exec conn "ROLLBACK"

      Row <- step stmt
      2 <- columnCount stmt
      [SQLInteger 3, SQLInteger 4] <- columns stmt
      Row <- step stmt
      2 <- columnCount stmt
      [SQLInteger 5, SQLInteger 6] <- columns stmt

      expectError ErrorLocked $ exec conn "DROP TABLE foo"
      withConnShared $ \conn ->
        expectError ErrorBusy $ exec conn "DROP TABLE foo"

      Done <- step stmt
      2 <- columnCount stmt
      exec conn "DROP TABLE foo"

      -- Regular 'reset' throws away the error.  Make sure sqlite3_reset did
      -- not return an error because foo is now gone.  sqlite3_reset should
      -- only return an error if the most recent 'step' failed.
      Right () <- Direct.reset stmt

      -- But trying to 'step' again should fail.
      Left SQLError{sqlError = err} <- try $ step stmt
      assertBool "Step after table vanishes should fail with SQLITE_ERROR or SQLITE_SCHEMA"
                 (err == ErrorError ||  -- SQLite 3.7.13
                  err == ErrorSchema)   -- SQLite 3.6.22

  where
    expectError err io = do
      Left SQLError{sqlError = err'} <- try io
      assertEqual "testErrors: expectError" err err'

    foo123456 conn =
      exec conn "CREATE TABLE foo (a INT, b INT); \
                \INSERT INTO foo VALUES (1, 2); \
                \INSERT INTO foo VALUES (3, 4); \
                \INSERT INTO foo VALUES (5, 6)"

-- Make sure data stored in a table comes back as-is.
testIntegrity :: TestEnv -> Test
testIntegrity TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    exec conn "CREATE TABLE foo (i INT, f FLOAT, t TEXT, b BLOB, n TEXT)"
    withStmt conn "INSERT INTO foo VALUES (?, ?, ?, ?, ?)" $ \insert ->
      withStmt conn "SELECT * FROM foo" $ \select -> do
        let test = testWith (===)

            testWith f values = do
              exec conn "DELETE FROM foo"

              reset insert
              bind insert values
              Done <- step insert

              reset select
              Row <- step select
              values' <- columns select
              Done <- step select

              return $ f values values'

        True <- test [SQLInteger 0, SQLFloat 0.0, SQLText T.empty, SQLBlob B.empty, SQLNull]
        True <- test [SQLInteger minBound, SQLFloat (-1/0), SQLText "\0", SQLBlob (B8.pack "\0"), SQLNull]
        True <- test [SQLInteger maxBound, SQLFloat (1/0), SQLText "\1114111", SQLBlob ("\255"), SQLNull]

        -- SQLite3 turns NaN into SQLNull.
        True <- testWith (\_old new -> new === [SQLNull, SQLNull, SQLNull, SQLNull, SQLNull])
                [SQLNull, SQLFloat (0/0), SQLNull, SQLNull, SQLNull]

        return ()

testDecodeError :: TestEnv -> Test
testDecodeError TestEnv{..} = TestCase $ do
  withStmt conn "SELECT ?" $ \stmt -> do
    Right () <- Direct.bindText stmt 1 invalidUtf8
    Row <- step stmt
    Left (DecodeError "Database.SQLite3.columnText: Invalid UTF-8" _)
      <- try $ column stmt 0
    return ()

  -- Verify the assertion that SQLite3 does not validate UTF-8, by writing the
  -- data to a table on disk and reading it back.
  withConnShared $ \conn -> do
    exec conn "CREATE TABLE testDecodeError (a TEXT)"
    withStmt conn "INSERT INTO testDecodeError VALUES (?)" $ \stmt -> do
      Right () <- Direct.bindText stmt 1 invalidUtf8
      Done <- step stmt
      return ()
  withConnShared $ \conn -> do
    withStmt conn "SELECT * FROM testDecodeError" $ \stmt -> do
      Row <- step stmt
      TextColumn <- columnType stmt 0
      txt <- Direct.columnText stmt 0
      assertEqual "testDecodeError: Database altered our invalid UTF-8" invalidUtf8 txt
      Left (DecodeError "Database.SQLite3.columnText: Invalid UTF-8" _)
        <- try $ columnText stmt 0
      Done <- step stmt
      return ()

  where
    invalidUtf8 = Direct.Utf8 $ B.pack [0x80]

testResultStats :: TestEnv -> Test
testResultStats TestEnv{..} = TestCase $
  withConn $ \conn -> do
    (0, 0, 0) <- stats conn
    exec conn "CREATE TABLE tbl (n INTEGER PRIMARY KEY)"
    (0, 0, 0) <- stats conn
    exec conn "INSERT INTO tbl DEFAULT VALUES"
    (1, 1, 1) <- stats conn
    exec conn "INSERT INTO tbl VALUES (123)"
    (123, 1, 2) <- stats conn
    exec conn "INSERT INTO tbl VALUES (9223372036854775807)"
    (maxBound, 1, 3) <- stats conn
    exec conn "INSERT INTO tbl DEFAULT VALUES"  -- picks a rowid at random
    (rowid, 1, 4) <- stats conn
    True <- return $ (`notElem` [1, 123, maxBound]) rowid
    exec conn "UPDATE tbl SET rowid=rowid+1 WHERE rowid=1 OR rowid=123"
    (_, 2, 6) <- stats conn
    Left SQLError{ sqlError = ErrorConstraint }
      <- try $ exec conn "UPDATE tbl SET rowid=4"
    exec conn "DELETE FROM tbl"
    (_, 4, 10) <- stats conn
    return ()
  where
    stats conn =
      liftM3 (,,) (lastInsertRowId conn)
                  (changes conn)
                  (Direct.totalChanges conn)

testGetAutoCommit :: TestEnv -> Test
testGetAutoCommit TestEnv{..} = TestCase $
  withConn $ \conn -> do
    True <- Direct.getAutoCommit conn
    exec conn "BEGIN"
    False <- Direct.getAutoCommit conn
    Left (ErrorError, _) <- Direct.exec conn "BEGIN"
    False <- Direct.getAutoCommit conn

    exec conn "ROLLBACK"
    True <- Direct.getAutoCommit conn
    Left (ErrorError, _) <- Direct.exec conn "ROLLBACK"
    True <- Direct.getAutoCommit conn

    exec conn "BEGIN"
    False <- Direct.getAutoCommit conn
    Left (ErrorFull, _) <- Direct.exec conn
        "PRAGMA max_page_count=1; CREATE TABLE foo (a INT)"
    True <- Direct.getAutoCommit conn
    Left (ErrorError, _) <- Direct.exec conn "ROLLBACK"

    return ()

testStatementSql :: TestEnv -> Test
testStatementSql TestEnv{..} = TestCase $ do
  let q1 = "SELECT 1+1"
  withStmt conn q1 $ \stmt -> do
    Just (Direct.Utf8 sql1) <- Direct.statementSql stmt
    T.encodeUtf8 q1 @=? sql1

testCustomFunction :: TestEnv -> Test
testCustomFunction TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    createFunction conn "repeat" (Just 2) True repeatString
    withStmt conn "SELECT repeat(3,'abc')" $ \stmt -> do
      Row <- step stmt
      [SQLText "abcabcabc"] <- columns stmt
      Done <- step stmt
      return ()
    deleteFunction conn "repeat" (Just 2)
    Left SQLError{sqlError = ErrorError} <-
        try $ exec conn "SELECT repeat(3,'abc')"
    return ()
  where
    repeatString ctx args = do
        n <- funcArgInt64 args 0
        s <- funcArgText args 1
        funcResultText ctx $ T.concat $ replicate (fromIntegral n) s

testCustomFunctionError :: TestEnv -> Test
testCustomFunctionError TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    createFunction conn "fail" (Just 0) True throwError
    Left SQLError{..} <- try $ exec conn "SELECT fail()"
    -- Match only the first 13 characters of the error message here.  The
    -- error message coming from the use of "error" nowadays contains
    -- fragments of the callstack and not just the string we gave it.
    assertBool "Catch exception"
        (sqlError == ErrorError && T.take 13 sqlErrorDetails == "error message")
  where
    throwError _ _ = error "error message"

testCustomAggragate :: TestEnv -> Test
testCustomAggragate TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    exec conn "CREATE TABLE tbl (n INT)"
    exec conn "INSERT INTO tbl(n) VALUES (12), (-3), (7)"
    createAggregate conn "mysum" (Just 1) 0 mySumStep funcResultInt64
    withStmt conn "SELECT mysum(n) FROM tbl" $ \stmt -> do
      Row <- step stmt
      [SQLInteger 16] <- columns stmt
      Done <- step stmt
      return ()
    deleteFunction conn "mysum" (Just 1)
    Left SQLError{sqlError = ErrorError} <-
        try $ exec conn "SELECT mysum(n) FROM tbl"
    return ()
  where
    mySumStep _ args s = do
        n <- funcArgInt64 args 0
        return (s + n)

testCustomCollation :: TestEnv -> Test
testCustomCollation TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    exec conn "CREATE TABLE tbl (n TEXT)"
    exec conn "INSERT INTO tbl(n) VALUES ('dog'),('mouse'),('ox'),('cat')"
    createCollation conn "len" cmpLen
    withStmt conn "SELECT * FROM tbl ORDER BY n COLLATE len" $ \stmt -> do
      Row <- step stmt
      [SQLText "ox"] <- columns stmt
      Row <- step stmt
      [SQLText "cat"] <- columns stmt
      Row <- step stmt
      [SQLText "dog"] <- columns stmt
      Row <- step stmt
      [SQLText "mouse"] <- columns stmt
      Done <- step stmt
      return ()
    deleteCollation conn "len"
    Left SQLError{sqlError = ErrorError} <-
        try $ exec conn "SELECT * FROM tbl ORDER BY n COLLATE len"
    return ()
  where
    -- order by length first, then by lexicographical order
    cmpLen s1 s2 = compare (T.length s1) (T.length s2) <> compare s1 s2

testIncrementalBlobIO :: TestEnv -> Test
testIncrementalBlobIO TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    exec conn "CREATE TABLE tbl (n BLOB)"
    exec conn "INSERT INTO tbl(rowid,n) VALUES (1,'abcdefg')"
    blob <- blobOpen conn "main" "tbl" "n" 1 True
    l <- blobBytes blob
    assertEqual "blobBytes" 7 l
    s <- blobRead blob 4 2
    assertEqual "blobRead" "cdef" s
    blobWrite blob "BC" 1
    blobClose blob
    withStmt conn "SELECT n FROM tbl" $ \stmt -> do
      Row <- step stmt
      s' <- columnBlob stmt 0
      assertEqual "blobWrite" "aBCdefg" s'

testInterrupt :: TestEnv -> Test
testInterrupt TestEnv{..} = TestCase $
  withConn $ \conn -> do
    exec conn "CREATE TABLE tbl (n INT)"

    withStmt conn "INSERT INTO tbl VALUES (?)" $ \stmt -> do
      exec conn "BEGIN"
      forM_ [1..200] $ \i -> do
          reset stmt
          bind stmt [SQLInteger i]
          Done <- step stmt
          return ()
      exec conn "COMMIT"

    stmt <- prepare conn tripleSum
    _ <- forkIO $ threadDelay 100000 >> interrupt conn
    Left ErrorInterrupt <- Direct.step stmt
    Left ErrorInterrupt <- Direct.finalize stmt

    Nothing <- timeout 100000 $ interruptibly conn $ exec conn tripleSum

    return ()

  where
    tripleSum = "SELECT sum(a.n + b.n + c.n) FROM tbl as a, tbl as b, tbl as c"

testMultiRowInsert :: TestEnv -> Test
testMultiRowInsert TestEnv{..} = TestCase $ do
  withConn $ \conn -> do
    exec conn "CREATE TABLE foo (a INT, b INT)"
    result <- try $ exec conn "INSERT INTO foo VALUES (1,2), (3,4)"
    case result of
      Left SQLError{sqlError = ErrorError} ->
        assertFailure "Installed SQLite3 does not support multi-row INSERT via the VALUES clause"
      Left e ->
        assertFailure $ show e
      Right () -> do
        -- Make sure multi-row insert actually worked
        2 <- changes conn
        withStmt conn "SELECT * FROM foo" $ \stmt -> do
          Row <- step stmt
          [SQLInteger 1, SQLInteger 2] <- columns stmt
          Row <- step stmt
          [SQLInteger 3, SQLInteger 4] <- columns stmt
          Done <- step stmt
          return ()


withTestEnv :: String -> (TestEnv -> IO a) -> IO a
withTestEnv tempDbName cb =
    withConn $ \conn ->
        cb TestEnv
            { conn           = conn
            , withConn       = withConn
            , withConnShared = withConnPath (T.pack tempDbName)
            }
  where
    withConn = withConnPath ":memory:"
    withConnPath path cb = do
      conn <- open path
      r <- cb conn `onException` Direct.close conn
            -- If the callback throws an exception, try to close the DB.
            -- If closing fails (usually due to open 'Statement's),
            -- throw the original error, not the error produced by 'close'.
            -- Direct.close returns the error rather than throwing it.
      close conn
      return r

runTestGroup :: String -> [TestEnv -> Test] -> IO Bool
runTestGroup tempDbName tests = do
  Counts{cases, tried, errors, failures} <-
    withTestEnv tempDbName $ \env -> runTestTT $ TestList $ map ($ env) tests
  return (cases == tried && errors == 0 && failures == 0)

main :: IO ()
main = do
  mapM_ (`hSetBuffering` LineBuffering) [stdout, stderr]
  withTempFile "." "direct-sqlite-test-database" $ \tempDbName _hFile -> do
    open (T.pack tempDbName) >>= close
    ok <- runTestGroup tempDbName regressionTests
    when (not ok) exitFailure
    -- Signal failure if feature tests fail.  I'd rather print a noisy warning
    -- instead, but cabal redirects test output to log files by default.
    ok <- runTestGroup tempDbName featureTests
    when (not ok) exitFailure
