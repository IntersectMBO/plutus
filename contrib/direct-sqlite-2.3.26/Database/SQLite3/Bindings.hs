{-# LANGUAGE ForeignFunctionInterface #-}
module Database.SQLite3.Bindings (
    module Database.SQLite3.Bindings.Types,

    -- * Connection management
    c_sqlite3_open,
    c_sqlite3_close,
    c_sqlite3_errcode,
    c_sqlite3_errmsg,
    c_sqlite3_interrupt,
    c_sqlite3_trace,
    CTraceCallback,
    mkCTraceCallback,
    c_sqlite3_get_autocommit,
    c_sqlite3_enable_shared_cache,

    -- * Simple query execution
    -- | <https://sqlite.org/c3ref/exec.html>
    c_sqlite3_exec,
    CExecCallback,
    mkCExecCallback,

    -- * Statement management
    c_sqlite3_prepare_v2,
    c_sqlite3_db_handle,
    c_sqlite3_step,
    c_sqlite3_step_unsafe,
    c_sqlite3_reset,
    c_sqlite3_finalize,
    c_sqlite3_clear_bindings,
    c_sqlite3_sql,

    -- * Parameter and column information
    c_sqlite3_bind_parameter_count,
    c_sqlite3_bind_parameter_name,
    c_sqlite3_bind_parameter_index,
    c_sqlite3_column_count,
    c_sqlite3_column_name,

    -- * Binding Values To Prepared Statements
    -- | <https://www.sqlite.org/c3ref/bind_blob.html>
    c_sqlite3_bind_blob,
    c_sqlite3_bind_zeroblob,
    c_sqlite3_bind_text,
    c_sqlite3_bind_double,
    c_sqlite3_bind_int64,
    c_sqlite3_bind_null,

    -- * Result Values From A Query
    -- | <https://www.sqlite.org/c3ref/column_blob.html>
    c_sqlite3_column_type,
    c_sqlite3_column_bytes,
    c_sqlite3_column_blob,
    c_sqlite3_column_int64,
    c_sqlite3_column_double,
    c_sqlite3_column_text,

    -- * Result statistics
    c_sqlite3_last_insert_rowid,
    c_sqlite3_changes,
    c_sqlite3_total_changes,

    -- * Create Or Redefine SQL Functions
    c_sqlite3_create_function_v2,
    CFunc,
    CFuncFinal,
    CFuncDestroy,
    mkCFunc,
    mkCFuncFinal,
    mkCFuncDestroy,
    c_sqlite3_user_data,
    c_sqlite3_context_db_handle,
    c_sqlite3_aggregate_context,

    -- * Obtaining SQL Function Parameter Values
    -- | <https://www.sqlite.org/c3ref/value_blob.html>
    c_sqlite3_value_type,
    c_sqlite3_value_bytes,
    c_sqlite3_value_blob,
    c_sqlite3_value_text,
    c_sqlite3_value_int64,
    c_sqlite3_value_double,

    -- * Setting The Result Of An SQL Function
    -- | <https://www.sqlite.org/c3ref/result_blob.html>
    c_sqlite3_result_null,
    c_sqlite3_result_blob,
    c_sqlite3_result_zeroblob,
    c_sqlite3_result_text,
    c_sqlite3_result_int64,
    c_sqlite3_result_double,
    c_sqlite3_result_value,
    c_sqlite3_result_error,

    -- * Define New Collating Sequences
    c_sqlite3_create_collation_v2,
    CCompare,
    mkCCompare,

    -- * Miscellaneous
    c_sqlite3_free,
    c_sqlite3_free_p,

    -- * Extensions
    c_sqlite3_enable_load_extension,

    -- * Write-Ahead Log Commit Hook
    c_sqlite3_wal_hook,
    CWalHook,
    mkCWalHook,

    -- * Incremental blob I/O
    c_sqlite3_blob_open,
    c_sqlite3_blob_close,
    c_sqlite3_blob_reopen,
    c_sqlite3_blob_bytes,
    c_sqlite3_blob_read,
    c_sqlite3_blob_write,

    -- * Online Backup API
    -- | <https://www.sqlite.org/backup.html> and
    -- <https://www.sqlite.org/c3ref/backup_finish.html>
    c_sqlite3_backup_init,
    c_sqlite3_backup_finish,
    c_sqlite3_backup_step,
    c_sqlite3_backup_remaining,
    c_sqlite3_backup_pagecount,
) where

import Database.SQLite3.Bindings.Types

import Foreign
import Foreign.C

-- | <https://www.sqlite.org/c3ref/open.html>
--
-- This sets the @'Ptr CDatabase'@ even on failure.
foreign import ccall "sqlite3_open"
    c_sqlite3_open :: CString -> Ptr (Ptr CDatabase) -> IO CError

-- | <https://www.sqlite.org/c3ref/close.html>
foreign import ccall "sqlite3_close"
    c_sqlite3_close :: Ptr CDatabase -> IO CError

-- | <https://www.sqlite.org/c3ref/errcode.html>
foreign import ccall unsafe "sqlite3_errcode"
    c_sqlite3_errcode :: Ptr CDatabase -> IO CError

-- | <https://www.sqlite.org/c3ref/errcode.html>
foreign import ccall unsafe "sqlite3_errmsg"
    c_sqlite3_errmsg :: Ptr CDatabase -> IO CString

-- | <https://www.sqlite.org/c3ref/interrupt.html>
foreign import ccall "sqlite3_interrupt"
    c_sqlite3_interrupt :: Ptr CDatabase -> IO ()

-- | <https://www.sqlite.org/c3ref/profile.html>
foreign import ccall "sqlite3_trace"
    c_sqlite3_trace
        :: Ptr CDatabase
        -> FunPtr (CTraceCallback a) -- ^ Optional callback function called for each row.
        -> Ptr a                     -- ^ Context passed to the callback.
        -> IO (Ptr ())               -- ^ Returns context pointer from previously.
                                     --   registered trace.

-- | <https://www.sqlite.org/c3ref/get_autocommit.html>
foreign import ccall unsafe "sqlite3_get_autocommit"
    c_sqlite3_get_autocommit :: Ptr CDatabase -> IO CInt

-- | <https://www.sqlite.org/c3ref/enable_shared_cache.html>
foreign import ccall unsafe "sqlite3_enable_shared_cache"
    c_sqlite3_enable_shared_cache :: Bool -> IO CError

-- | <https://www.sqlite.org/c3ref/exec.html>
foreign import ccall "sqlite3_exec"
    c_sqlite3_exec
        :: Ptr CDatabase
        -> CString                  -- ^ SQL statement, UTF-8 encoded.
        -> FunPtr (CExecCallback a) -- ^ Optional callback function called for each row.
        -> Ptr a                    -- ^ Context passed to the callback.
        -> Ptr CString              -- ^ OUT: Error message string.
        -> IO CError

type CExecCallback a
     = Ptr a
    -> CColumnCount -- ^ Number of columns, which is the number of elements in
                    --   the following arrays.
    -> Ptr CString  -- ^ Array of column values, as returned by
                    --   'c_sqlite3_column_text'.  Null values are represented
                    --   as null pointers.
    -> Ptr CString  -- ^ Array of column names
    -> IO CInt      -- ^ If the callback returns non-zero, then
                    --   'c_sqlite3_exec' returns @SQLITE_ABORT@
                    --   ('ErrorAbort').

type CTraceCallback a
     = Ptr a
    -> CString      -- ^ UTF-8 rendering of the SQL statement text as
                    --   the statement first begins executing.
    -> IO ()

-- | A couple important things to know about callbacks from Haskell code:
--
--  * If the callback throws an exception, apparently, the /whole program/ is
--    terminated.
--
--  * Remember to call 'freeHaskellFunPtr' when you are done with the wrapper,
--    to avoid leaking memory.
foreign import ccall "wrapper"
    mkCExecCallback :: CExecCallback a -> IO (FunPtr (CExecCallback a))

foreign import ccall "wrapper"
    mkCTraceCallback :: CTraceCallback a -> IO (FunPtr (CTraceCallback a))

-- | <https://www.sqlite.org/c3ref/prepare.html>
--
-- If the query contains no SQL statements, this returns @SQLITE_OK@ and sets
-- the @'Ptr' 'CStatement'@ to null.
foreign import ccall "sqlite3_prepare_v2"
    c_sqlite3_prepare_v2
        :: Ptr CDatabase
        -> CString              -- ^ SQL statement, UTF-8 encoded.
        -> CNumBytes            -- ^ Maximum length of the SQL statement,
                                --   in bytes.  If this is negative, then the
                                --   SQL statement is treated as a
                                --   NUL-terminated string.
        -> Ptr (Ptr CStatement) -- ^ OUT: Statement handle.  This must not be null.
        -> Ptr CString          -- ^ OUT: Pointer to unused portion of zSql.
        -> IO CError

-- | <https://www.sqlite.org/c3ref/db_handle.html>
foreign import ccall unsafe "sqlite3_db_handle"
    c_sqlite3_db_handle :: Ptr CStatement -> IO (Ptr CDatabase)

-- | <https://www.sqlite.org/c3ref/step.html>
foreign import ccall "sqlite3_step"
    c_sqlite3_step :: Ptr CStatement -> IO CError

-- | <https://www.sqlite.org/c3ref/step.html>
foreign import ccall unsafe "sqlite3_step"
    c_sqlite3_step_unsafe :: Ptr CStatement -> IO CError

-- | <https://www.sqlite.org/c3ref/reset.html>
--
-- /Warning:/ If the most recent 'c_sqlite3_step' call failed,
-- this will return the corresponding error code.
foreign import ccall unsafe "sqlite3_reset"
    c_sqlite3_reset :: Ptr CStatement -> IO CError

-- | <https://www.sqlite.org/c3ref/finalize.html>
--
-- /Warning:/ If the most recent 'c_sqlite3_step' call failed,
-- this will return the corresponding error code.
foreign import ccall "sqlite3_finalize"
    c_sqlite3_finalize :: Ptr CStatement -> IO CError

-- | <https://www.sqlite.org/c3ref/clear_bindings.html>
--
-- A look at the source reveals that this function always returns @SQLITE_OK@.
foreign import ccall unsafe "sqlite3_clear_bindings"
    c_sqlite3_clear_bindings :: Ptr CStatement -> IO CError

-- | <https://www.sqlite.org/c3ref/sql.html>
foreign import ccall unsafe "sqlite3_sql"
    c_sqlite3_sql :: Ptr CStatement -> IO CString

-- | <https://www.sqlite.org/c3ref/bind_parameter_count.html>
--
-- This returns the index of the largest (rightmost) parameter, which is not
-- necessarily the number of parameters.  If numbered parameters like @?5@
-- are used, there may be gaps in the list.
foreign import ccall unsafe "sqlite3_bind_parameter_count"
    c_sqlite3_bind_parameter_count :: Ptr CStatement -> IO CParamIndex

-- | <https://www.sqlite.org/c3ref/bind_parameter_name.html>
foreign import ccall unsafe "sqlite3_bind_parameter_name"
    c_sqlite3_bind_parameter_name :: Ptr CStatement -> CParamIndex -> IO CString

-- | <https://www.sqlite.org/c3ref/bind_parameter_index.html>
foreign import ccall unsafe "sqlite3_bind_parameter_index"
    c_sqlite3_bind_parameter_index :: Ptr CStatement -> CString -> IO CParamIndex

-- | <https://www.sqlite.org/c3ref/column_count.html>
foreign import ccall unsafe "sqlite3_column_count"
    c_sqlite3_column_count :: Ptr CStatement -> IO CColumnCount

-- | <https://www.sqlite.org/c3ref/column_name.html>
foreign import ccall unsafe "sqlite3_column_name"
    c_sqlite3_column_name :: Ptr CStatement -> CColumnIndex -> IO CString

-- | <https://www.sqlite.org/c3ref/bind_blob.html>
foreign import ccall unsafe "sqlite3_bind_blob"
    c_sqlite3_bind_blob
        :: Ptr CStatement
        -> CParamIndex      -- ^ Index of the SQL parameter to be set
        -> Ptr a            -- ^ Value to bind to the parameter.
                            --
                            --   /Warning:/ If this pointer is @NULL@, this
                            --   will bind a null value, rather than an empty blob.
        -> CNumBytes        -- ^ Length, in bytes.  This must not be negative.
        -> Ptr CDestructor
        -> IO CError

-- | <https://www.sqlite.org/c3ref/bind_blob.html>
foreign import ccall unsafe "sqlite3_bind_zeroblob"
    c_sqlite3_bind_zeroblob
        :: Ptr CStatement -> CParamIndex -> CInt -> IO CError

-- | <https://www.sqlite.org/c3ref/bind_blob.html>
foreign import ccall unsafe "sqlite3_bind_text"
    c_sqlite3_bind_text
        :: Ptr CStatement
        -> CParamIndex
        -> CString          -- ^ /Warning:/ If this pointer is @NULL@, this
                            --   will bind a null value, rather than an empty text.
        -> CNumBytes        -- ^ Length, in bytes.  If this is negative,
                            --   the value is treated as a NUL-terminated string.
        -> Ptr CDestructor
        -> IO CError

-- | <https://www.sqlite.org/c3ref/bind_blob.html>
foreign import ccall unsafe "sqlite3_bind_double"
    c_sqlite3_bind_double   :: Ptr CStatement -> CParamIndex -> Double -> IO CError

-- | <https://www.sqlite.org/c3ref/bind_blob.html>
foreign import ccall unsafe "sqlite3_bind_int64"
    c_sqlite3_bind_int64    :: Ptr CStatement -> CParamIndex -> Int64 -> IO CError

-- | <https://www.sqlite.org/c3ref/bind_blob.html>
foreign import ccall unsafe "sqlite3_bind_null"
    c_sqlite3_bind_null     :: Ptr CStatement -> CParamIndex -> IO CError

-- | <https://www.sqlite.org/c3ref/column_blob.html>
foreign import ccall unsafe "sqlite3_column_type"
    c_sqlite3_column_type   :: Ptr CStatement -> CColumnIndex -> IO CColumnType

-- | <https://www.sqlite.org/c3ref/column_blob.html>
foreign import ccall unsafe "sqlite3_column_bytes"
    c_sqlite3_column_bytes  :: Ptr CStatement -> CColumnIndex -> IO CNumBytes

-- | <https://www.sqlite.org/c3ref/column_blob.html>
foreign import ccall unsafe "sqlite3_column_blob"
    c_sqlite3_column_blob   :: Ptr CStatement -> CColumnIndex -> IO (Ptr a)

-- | <https://www.sqlite.org/c3ref/column_blob.html>
foreign import ccall unsafe "sqlite3_column_text"
    c_sqlite3_column_text   :: Ptr CStatement -> CColumnIndex -> IO CString

-- | <https://www.sqlite.org/c3ref/column_blob.html>
foreign import ccall unsafe "sqlite3_column_int64"
    c_sqlite3_column_int64  :: Ptr CStatement -> CColumnIndex -> IO Int64

-- | <https://www.sqlite.org/c3ref/column_blob.html>
foreign import ccall unsafe "sqlite3_column_double"
    c_sqlite3_column_double :: Ptr CStatement -> CColumnIndex -> IO Double

-- | <https://www.sqlite.org/c3ref/last_insert_rowid.html>
foreign import ccall unsafe "sqlite3_last_insert_rowid"
    c_sqlite3_last_insert_rowid :: Ptr CDatabase -> IO Int64

-- | <https://www.sqlite.org/c3ref/changes.html>
foreign import ccall unsafe "sqlite3_changes"
    c_sqlite3_changes :: Ptr CDatabase -> IO CInt

-- | <https://www.sqlite.org/c3ref/total_changes.html>
foreign import ccall unsafe "sqlite3_total_changes"
    c_sqlite3_total_changes :: Ptr CDatabase -> IO CInt

-- do not use unsafe import here, it might call back to haskell
-- via the CFuncDestroy argument
-- | <https://sqlite.org/c3ref/create_function.html>
foreign import ccall "sqlite3_create_function_v2"
    c_sqlite3_create_function_v2
        :: Ptr CDatabase
        -> CString         -- ^ Name of the function.
        -> CArgCount       -- ^ Number of arguments.
        -> CInt            -- ^ Preferred text encoding (also used to pass flags).
        -> Ptr a           -- ^ User data.
        -> FunPtr CFunc
        -> FunPtr CFunc
        -> FunPtr CFuncFinal
        -> FunPtr (CFuncDestroy a)
        -> IO CError

type CFunc          = Ptr CContext -> CArgCount -> Ptr (Ptr CValue) -> IO ()

type CFuncFinal     = Ptr CContext -> IO ()

type CFuncDestroy a = Ptr a -> IO ()

foreign import ccall "wrapper"
    mkCFunc        :: CFunc          -> IO (FunPtr CFunc)

foreign import ccall "wrapper"
    mkCFuncFinal   :: CFuncFinal     -> IO (FunPtr CFuncFinal)

foreign import ccall "wrapper"
    mkCFuncDestroy :: CFuncDestroy a -> IO (FunPtr (CFuncDestroy a))

-- | <https://www.sqlite.org/c3ref/user_data.html>
foreign import ccall unsafe "sqlite3_user_data"
    c_sqlite3_user_data :: Ptr CContext -> IO (Ptr a)

-- | <https://www.sqlite.org/c3ref/context_db_handle.html>
foreign import ccall unsafe "sqlite3_context_db_handle"
    c_sqlite3_context_db_handle :: Ptr CContext -> IO (Ptr CDatabase)

-- | <https://www.sqlite.org/c3ref/aggregate_context.html>
foreign import ccall unsafe "sqlite3_aggregate_context"
    c_sqlite3_aggregate_context :: Ptr CContext -> CNumBytes -> IO (Ptr a)

-- | <https://www.sqlite.org/c3ref/value_blob.html>
foreign import ccall unsafe "sqlite3_value_type"
    c_sqlite3_value_type   :: Ptr CValue -> IO CColumnType

-- | <https://www.sqlite.org/c3ref/value_blob.html>
foreign import ccall unsafe "sqlite3_value_bytes"
    c_sqlite3_value_bytes  :: Ptr CValue -> IO CNumBytes

-- | <https://www.sqlite.org/c3ref/value_blob.html>
foreign import ccall unsafe "sqlite3_value_blob"
    c_sqlite3_value_blob   :: Ptr CValue -> IO (Ptr a)

-- | <https://www.sqlite.org/c3ref/value_blob.html>
foreign import ccall unsafe "sqlite3_value_text"
    c_sqlite3_value_text   :: Ptr CValue -> IO CString

-- | <https://www.sqlite.org/c3ref/value_blob.html>
foreign import ccall unsafe "sqlite3_value_int64"
    c_sqlite3_value_int64  :: Ptr CValue -> IO Int64

-- | <https://www.sqlite.org/c3ref/value_blob.html>
foreign import ccall unsafe "sqlite3_value_double"
    c_sqlite3_value_double :: Ptr CValue -> IO Double

-- | <https://www.sqlite.org/c3ref/result_blob.html>
foreign import ccall unsafe "sqlite3_result_null"
    c_sqlite3_result_null     :: Ptr CContext -> IO ()

-- | <https://www.sqlite.org/c3ref/result_blob.html>
foreign import ccall unsafe "sqlite3_result_blob"
    c_sqlite3_result_blob     :: Ptr CContext -> Ptr a -> CNumBytes -> Ptr CDestructor -> IO ()

-- | <https://www.sqlite.org/c3ref/result_blob.html>
foreign import ccall unsafe "sqlite3_result_zeroblob"
    c_sqlite3_result_zeroblob :: Ptr CContext -> CNumBytes -> IO ()

-- | <https://www.sqlite.org/c3ref/result_blob.html>
foreign import ccall unsafe "sqlite3_result_text"
    c_sqlite3_result_text     :: Ptr CContext -> CString -> CNumBytes -> Ptr CDestructor -> IO ()

-- | <https://www.sqlite.org/c3ref/result_blob.html>
foreign import ccall unsafe "sqlite3_result_int64"
    c_sqlite3_result_int64    :: Ptr CContext -> Int64 -> IO ()

-- | <https://www.sqlite.org/c3ref/result_blob.html>
foreign import ccall unsafe "sqlite3_result_double"
    c_sqlite3_result_double   :: Ptr CContext -> Double -> IO ()

-- | <https://www.sqlite.org/c3ref/result_blob.html>
foreign import ccall unsafe "sqlite3_result_value"
    c_sqlite3_result_value    :: Ptr CContext -> Ptr CValue -> IO ()

-- | <https://www.sqlite.org/c3ref/result_blob.html>
foreign import ccall unsafe "sqlite3_result_error"
    c_sqlite3_result_error    :: Ptr CContext -> CString -> CNumBytes -> IO ()

-- | <https://www.sqlite.org/c3ref/create_collation.html>
foreign import ccall "sqlite3_create_collation_v2"
    c_sqlite3_create_collation_v2
        :: Ptr CDatabase
        -> CString         -- ^ Name of the collation.
        -> CInt            -- ^ Text encoding.
        -> Ptr a           -- ^ User data.
        -> FunPtr (CCompare a)
        -> FunPtr (CFuncDestroy a)
        -> IO CError

type CCompare a = Ptr a -> CNumBytes -> CString -> CNumBytes -> CString -> IO CInt

foreign import ccall "wrapper"
    mkCCompare :: CCompare a -> IO (FunPtr (CCompare a))

-- | <https://sqlite.org/c3ref/free.html>
foreign import ccall "sqlite3_free"
    c_sqlite3_free :: Ptr a -> IO ()

-- | <https://sqlite.org/c3ref/free.html>
foreign import ccall "&sqlite3_free"
    c_sqlite3_free_p :: FunPtr (Ptr a -> IO ())

-- | <https://sqlite.org/c3ref/enable_load_extension.html>
foreign import ccall "sqlite3_enable_load_extension"
    c_sqlite3_enable_load_extension :: Ptr CDatabase -> Bool -> IO CError

-- | <https://www.sqlite.org/c3ref/wal_hook.html>
foreign import ccall unsafe "sqlite3_wal_hook"
    c_sqlite3_wal_hook :: Ptr CDatabase -> FunPtr CWalHook -> Ptr a -> IO (Ptr ())

type CWalHook = Ptr () -> Ptr CDatabase -> CString -> CInt -> IO CError

foreign import ccall "wrapper"
    mkCWalHook :: CWalHook -> IO (FunPtr CWalHook)

-- | <https://www.sqlite.org/c3ref/blob_open.html>
foreign import ccall unsafe "sqlite3_blob_open"
    c_sqlite3_blob_open
        :: Ptr CDatabase
        -> CString         -- ^ Database name.
        -> CString         -- ^ Table name.
        -> CString         -- ^ Column name.
        -> Int64           -- ^ Row ROWID.
        -> CInt            -- ^ Flags.
        -> Ptr (Ptr CBlob) -- ^ OUT: Blob handle, will be NULL on error.
        -> IO CError

-- | <https://www.sqlite.org/c3ref/blob_close.html>
foreign import ccall unsafe "sqlite3_blob_close"
    c_sqlite3_blob_close :: Ptr CBlob -> IO CError

-- | <https://www.sqlite.org/c3ref/blob_reopen.html>
foreign import ccall unsafe "sqlite3_blob_reopen"
    c_sqlite3_blob_reopen :: Ptr CBlob -> Int64 -> IO CError

-- | <https://www.sqlite.org/c3ref/blob_bytes.html>
foreign import ccall unsafe "sqlite3_blob_bytes"
    c_sqlite3_blob_bytes :: Ptr CBlob -> IO CInt

-- | <https://www.sqlite.org/c3ref/blob_read.html>
foreign import ccall unsafe "sqlite3_blob_read"
    c_sqlite3_blob_read :: Ptr CBlob -> Ptr a -> CInt -> CInt -> IO CError

-- | <https://www.sqlite.org/c3ref/blob_write.html>
foreign import ccall unsafe "sqlite3_blob_write"
    c_sqlite3_blob_write :: Ptr CBlob -> Ptr a -> CInt -> CInt -> IO CError

-- | <https://www.sqlite.org/c3ref/backup_finish.html#sqlite3backupinit>
foreign import ccall "sqlite3_backup_init"
    c_sqlite3_backup_init
        :: Ptr CDatabase  -- ^ Destination database handle.
        -> CString        -- ^ Destination database name.
        -> Ptr CDatabase  -- ^ Source database handle.
        -> CString        -- ^ Source database name.
        -> IO (Ptr CBackup)

-- | <https://www.sqlite.org/c3ref/backup_finish.html#sqlite3backupfinish>
foreign import ccall "sqlite3_backup_finish"
    c_sqlite3_backup_finish :: Ptr CBackup -> IO CError

-- | <https://www.sqlite.org/c3ref/backup_finish.html#sqlite3backupstep>
foreign import ccall unsafe "sqlite3_backup_step"
    c_sqlite3_backup_step :: Ptr CBackup -> CInt -> IO CError

-- | <https://www.sqlite.org/c3ref/backup_finish.html#sqlite3backupremaining>
foreign import ccall unsafe "sqlite3_backup_remaining"
    c_sqlite3_backup_remaining :: Ptr CBackup -> IO CInt

-- | <https://www.sqlite.org/c3ref/backup_finish.html#sqlite3backuppagecount>
foreign import ccall unsafe "sqlite3_backup_pagecount"
    c_sqlite3_backup_pagecount :: Ptr CBackup -> IO CInt
