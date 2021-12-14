#!/usr/bin/env bash

set -euo pipefail

# build cryptonite and cardano-crypto C sources with emscripten

# first run symlink the cbits subdirs of the cryptonite and cardano-crypto packages:
#  ln -s ../cryptonite/cbits cryptonite
#  ln -s ../cardano-crypto/cbits cardano-crypto

NAME=direct-sqlite

emcc -o $NAME.js -s WASM=0 \
  -s ALLOW_TABLE_GROWTH \
  -s "EXPORTED_RUNTIME_METHODS=['printErr','addFunction','removeFunction','getTempRet0','setTempRet0']" \
  -s "EXPORTED_FUNCTIONS=['_malloc', '_free',\
                         '_sqlite3_open',
                         '_sqlite3_close',
                         '_sqlite3_errcode',
                         '_sqlite3_errmsg',
                         '_sqlite3_interrupt',
                         '_sqlite3_trace',
                         '_sqlite3_get_autocommit',
                         '_sqlite3_enable_shared_cache',
                         '_sqlite3_exec',
                         '_sqlite3_prepare_v2',
                         '_sqlite3_db_handle',
                         '_sqlite3_step',
                         '_sqlite3_reset',
                         '_sqlite3_finalize',
                         '_sqlite3_clear_bindings',
                         '_sqlite3_sql',
                         '_sqlite3_bind_parameter_count',
                         '_sqlite3_bind_parameter_name',
                         '_sqlite3_bind_parameter_index',
                         '_sqlite3_column_count',
                         '_sqlite3_column_name',
                         '_sqlite3_bind_blob',
                         '_sqlite3_bind_zeroblob',
                         '_sqlite3_bind_text',
                         '_sqlite3_bind_double',
                         '_sqlite3_bind_int64',
                         '_sqlite3_bind_null',
                         '_sqlite3_column_type',
                         '_sqlite3_column_bytes',
                         '_sqlite3_column_blob',
                         '_sqlite3_column_text',
                         '_sqlite3_column_int64',
                         '_sqlite3_column_double',
                         '_sqlite3_last_insert_rowid',
                         '_sqlite3_changes',
                         '_sqlite3_total_changes',
                         '_sqlite3_create_function_v2',
                         '_sqlite3_user_data',
                         '_sqlite3_context_db_handle',
                         '_sqlite3_aggregate_context',
                         '_sqlite3_value_type',
                         '_sqlite3_value_bytes',
                         '_sqlite3_value_blob',
                         '_sqlite3_value_text',
                         '_sqlite3_value_int64',
                         '_sqlite3_value_double',
                         '_sqlite3_result_null',
                         '_sqlite3_result_blob',
                         '_sqlite3_result_zeroblob',
                         '_sqlite3_result_text',
                         '_sqlite3_result_int64',
                         '_sqlite3_result_double',
                         '_sqlite3_result_value',
                         '_sqlite3_result_error',
                         '_sqlite3_create_collation_v2',
                         '_sqlite3_free',
                         '_sqlite3_enable_load_extension',
                         '_sqlite3_wal_hook',
                         '_sqlite3_blob_open',
                         '_sqlite3_blob_close',
                         '_sqlite3_blob_reopen',
                         '_sqlite3_blob_bytes',
                         '_sqlite3_blob_read',
                         '_sqlite3_blob_write',
                         '_sqlite3_backup_init',
                         '_sqlite3_backup_finish',
                         '_sqlite3_backup_step',
                         '_sqlite3_backup_remaining',
                         '_sqlite3_backup_pagecount' ]" \
  -I. -I../../cbits \
  ../../cbits/sqlite3.c

# closure-compiler --js=$NAME.js --js_output_file=$NAME.min.js

cat $NAME.pre.js $NAME.js $NAME.post.js $NAME-wrappers.js > ../$NAME.js
