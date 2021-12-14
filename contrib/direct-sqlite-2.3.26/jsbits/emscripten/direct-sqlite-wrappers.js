/*
  Pointers in emscripten compiled code are represented as offsets
  into the global HEAP ArrayBuffer.

  GHCJS pointers (Addr#) and unlifted arrays (ByteArray# etc.) are represented
  as a pair of a buffer and an offset.
 */

  function h$logWrapper(x) {
    /* console.log(x); */
  }

  h$direct_sqlite.h$copyToHeap = function(buf_d, buf_o, tgt, len) {
    if(len === 0) return;
    var u8 = buf_d.u8;
    var hexes = "";
    for(var i=0;i<len;i++) {
      h$direct_sqlite.HEAPU8[tgt+i] = u8[buf_o+i];
      hexes += h$toHex(u8[buf_o+i]);
    }
    // h$logWrapper("=> " + len + " " + hexes + " " + buf_o + " " + buf_d.len);
  }

  h$direct_sqlite.h$copyFromHeap = function(src, buf_d, buf_o, len) {
    var u8 = buf_d.u8;
    var hexes = "";
    for(var i=0;i<len;i++) {
      u8[buf_o+i] = h$direct_sqlite.HEAPU8[src+i];
      hexes += h$toHex(h$direct_sqlite.HEAPU8[src+i]);
    }
    // h$logWrapper("<= " + len + " " + hexes + " " + buf_o + " " + buf_d.len);
  }

  function h$toHex(n) {
    var s = n.toString(16);
    if(s.length === 1) s = '0' + s;
    return s;
  }

  var h$buffers     = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
  var h$bufferSizes = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];

  h$direct_sqlite.h$getTmpBuffer = function(n, minSize) {
    var sn = h$bufferSizes[n];
    if(sn < minSize) {
      if(sn > 0) {
        h$direct_sqlite._free(h$buffers[n]);
      }
      h$buffers[n] = h$direct_sqlite._malloc(2*minSize); // fixme 2* shouldn't be needed
      h$bufferSizes[n] = minSize;
    }
    return h$buffers[n];
  }

  h$direct_sqlite.h$getTmpBufferWith = function(n, buf_d, buf_o, len) {
    // fixme: we can avoid the copying if the buffer is already the actual
    //        heap buffer
    var buf_ptr = h$direct_sqlite.h$getTmpBuffer(n, len);
    h$direct_sqlite.h$copyToHeap(buf_d, buf_o, buf_ptr, len);
    return buf_ptr;
  }


  h$direct_sqlite.h$copyStringToHeap = function(n, str_d, str_o) {
    if(str_d === null) return null;
    return ptr = h$direct_sqlite.h$getTmpBufferWith(n, str_d, str_o, str_d.len);
  }

  h$direct_sqlite.h$withCString = function(str_d, str_o, cont) {
    return h$direct_sqlite.h$withCBuffer(str_d, str_o, str_d === null ? 0 : str_d.len, cont);
  }

  h$direct_sqlite.h$withCBuffer = function(str_d, str_o, len, cont) {
    var str = h$direct_sqlite._malloc(len);
    if(str_d !== null) h$direct_sqlite.h$copyToHeap(str_d, str_o, str, len);
    var ret = cont(str);
    h$direct_sqlite._free(str);
    return ret;
  }

  h$direct_sqlite.h$withOutBuffer = function(ptr_d, ptr_o, len, cont) {
    var ptr = h$direct_sqlite._malloc(len);
    h$direct_sqlite.h$copyToHeap(ptr_d, ptr_o, ptr, len);
    var ret = cont(ptr);
    h$direct_sqlite.h$copyFromHeap(ptr, ptr_d, ptr_o, len);
    h$direct_sqlite._free(ptr);
    return ret;
  }

  h$direct_sqlite.h$withFunction = function(stbl_ptr, g, cont) {
    var f = h$deRefStablePtr(stbl_ptr);
    if(f === null) return cont(null);
    // g takes as first argument the "real" function we want to call.
    var fptr = h$direct_sqlite.addFunction(g.bind(null,f));
    var ret = cont(fptr);
    h$direct_sqlite.removeFunction(fptr);
    return ret;
  }

  h$direct_sqlite.h$debugHeapStr = function(offset) {
    var len = 0;
    while(this.HEAPU8[offset+len] !== 0){ len++; };
    return new TextDecoder("utf-8").decode(h$direct_sqlite.HEAPU8.subarray(offset, offset+len+1));
  }

  h$direct_sqlite.h$cstring = function(offset) {
    if(offset == 0) return null;
    var len = 0;
    while(this.HEAPU8[offset+len] !== 0){ len++; };
    var str = h$newByteArray(len+1);
    str.u8.set(this.HEAPU8.subarray(offset,offset+len+1));
    return str;
  }

  h$direct_sqlite.h$ptr = function(offset) {
    var ptr = h$newByteArray(4);
    ptr.u8.set(this.HEAPU8.subarray(offset, offset+4));
    return ptr;
  }

  h$direct_sqlite.h$nptr = function(offset,n) {
    var ptr = h$newByteArray(4*n);
    ptr.u8.set(this.HEAPU8.subarray(offset, offset+4*n));
    return ptr;
  }

  // sqlite3_open ::  CString -> Ptr (Ptr CDatabase) -> IO CError
  function h$sqlite3_open(str_d, str_o, db_d, db_o) {
    var str = h$direct_sqlite.h$copyStringToHeap(0, str_d, str_o);
        ptr = h$direct_sqlite.h$getTmpBufferWith(1, db_d, db_o, 4);
        ret = h$direct_sqlite._sqlite3_open(str, ptr);

    // make sure to return a pointer! Needs to be a pair! ([d,0])
    db_d.arr = [[h$direct_sqlite.h$ptr(ptr),0]];
    return ret;
  }

  // sqlite3_close :: Ptr CDatabase -> IO CError
  function h$sqlite3_close(db_d, db_o) {
    var ptr = db_d.i3[0];
    return h$direct_sqlite._sqlite3_close(ptr);
  }

  // sqlite3_errcode :: Ptr CDatabase -> IO CError
  function h$sqlite3_errcode(db_d, db_o) {
    var ptr = db_d.i3[0];
    return h$direct_sqlite._sqlite3_close(ptr);
  }

  // sqlite3_interrupt :: Ptr CDatabase -> IO ()
  function h$sqlite3_interrupt(db_d, db_o) {
    var ptr = db_d.i3[0];
    // we don't really need to return here. it's unit.
    return h$direct_sqlite._sqlite3_interrupt(ptr);
  }

  // sqlite3_errmsg :: Ptr CDatabase -> IO CString
  function h$sqlite3_errmsg(db_d, db_o) {
    var ptr = db_d.i3[0];
        charptr = h$direct_sqlite._sqlite3_errmsg(ptr);
    return h$direct_sqlite.h$cstring(charptr);
  }
  // sqlite3_trace :: Ptr CDatabase -> FunPtr (CTraceCallback a)  -> Ptr a -> IO (Ptr ())
  function h$sqlite3_trace(db_d, db_o, cb_ptr_d, cb_ptr_o, ctx_d, ctx_o) {
    // we'll pass the ctx to the callback as the first argument, the string as the second.
    var cb = null;
        cb_ptr = null;
    if(cb_ptr_o !== 0) {
      cb = h$deRefStablePtr(cb_ptr_o);
      cb_ = function(ctx_ptr, str) {
        var ctx_ptr_ = h$direct_sqlite.h$ptr(ctx_ptr);
            str_ = h$direct_sqlite.h$cstring(str);
        var res = cb(ctx_ptr_, str_);
        return res;
      };
      cb_ptr = h$direct_sqlite.addFunction(cb_);
    }
    var ctx_ptr = ctx_d === null ? null : h$direct_sqlite.h$getTmpBufferWith(0, ctx_d, ctx_o, 4);
        ret = h$direct_sqlite._sqlite3_trace(db_d.i3[0], cb_ptr, ctx_ptr);

    if(cb_ptr !== null) {
      h$direct_sqlite.removeFunction(cb_ptr);
    }
    return h$direct_sqlite.h$ptr(ret);
  }
  // sqlite3_get_autocommit :: Ptr CDatabase -> IO CInt
  function h$sqlite3_get_autocommit(db_d, db_o) {
    return h$direct_sqlite._sqlite3_get_autocommit(db_d.i3[0]);
  }
  // sqlite3_enable_shared_cache :: Bool -> IO CError
  // sqlite3_exec :: Ptr CDatabase
  //              -> CString
  //              -> FunPtr (CExecCallback a)
  //              -> Ptr a
  //              -> Ptr CString
  //              -> IO CError
  function h$sqlite3_exec(db_d, db_o,
                          sql_d, sql_o,
                          stbl_buf, stbl_ptr,
                          ptr_d, ptr_o,
                          res_d, res_o) {

                          //   type CExecCallback a
                          //   = Ptr a
                          //  -> CColumnCount -- ^ Number of columns, which is the number of elements in
                          //                  --   the following arrays.
                          //  -> Ptr CString  -- ^ Array of column values, as returned by
                          //                  --   'c_sqlite3_column_text'.  Null values are represented
                          //                  --   as null pointers.
                          //  -> Ptr CString  -- ^ Array of column names
                          //  -> IO CInt      -- ^ If the callback returns non-zero, then
                          //                  --   'c_sqlite3_exec' returns @SQLITE_ABORT@
                          //                  --   ('ErrorAbort').


    var cb = null;
        cb_ptr = null;
    if(stbl_ptr !== 0) {
        // console.log(stbl_buf, stbl_ptr);
        cb = h$deRefStablePtr(stbl_ptr);
        cb_ = function(ctx_ptr, col_count, cval_ptr, ccol_ptr) {
          // So the function *C* will call will return something like this:
          //        HEAPU8
          //      .--------.
          //      |  ctx* -|-> [context_sized byte array]
          //      |  n     |
          //    .-|- val*  |
          //  .-|-|  col*  |
          //  | | /--------/
          //  | '>| val[0]-|-> CString
          //  |   | val[1]-|-> CString
          //  |   / ...    /
          //  |   | val[n]-|-> CString
          //  |   /--------/
          //  '-->| col[0]-|-> CString
          //      | col[1]-|-> CString
          //      / ...    /
          //      | col[n]-|-> CString
          //      '--------'
          var ctx_ptr_ = h$direct_sqlite.h$ptr(ctx_ptr);
              cval_ptr_ = h$direct_sqlite.h$nptr(cval_ptr, col_count);
              ccol_ptr_ = h$direct_sqlite.h$nptr(ccol_ptr, col_count);

          // populate the arrays. We need alignment of 4 here.
          cval_ptr_.arr = [];
          for(var i = 0; i < col_count; i++) {
            // we need to pad to 4 elements.
            var value = cval_ptr_.i3[i] === 0 ? null : [h$direct_sqlite.h$cstring(cval_ptr_.i3[i]),0];
            cval_ptr_.arr = cval_ptr_.arr.concat([value, null, null, null]);
          }
          ccol_ptr_.arr = [];
          for(var i = 0; i < col_count; i++) {
            // we need to pad to 4 elements.
            var value = ccol_ptr_.i3[i] === 0 ? null : [h$direct_sqlite.h$cstring(ccol_ptr_.i3[i]),0];
            ccol_ptr_.arr = ccol_ptr_.arr.concat([value, null, null, null]);
          }
          var res = cb(ctx_ptr_, col_count, cval_ptr_, ccol_ptr_);
          return res;
        };
        cb_ptr = h$direct_sqlite.addFunction(cb_);
    }
    return h$direct_sqlite.h$withCString(sql_d, sql_o, function(sql) {
      // console.log("exec", h$direct_sqlite.h$debugHeapStr(sql));

      var ptr_ptr = ptr_d === null ? null : h$direct_sqlite.h$getTmpBufferWith(2, ptr_d, ptr_o, 4);
      var ret = h$direct_sqlite.h$withOutBuffer(res_d, res_o, 4, function(res_ptr) {
            return h$direct_sqlite._sqlite3_exec(db_d.i3[0], sql, cb_ptr, null, res_ptr);
          });
      // I don't think we need to read back anything from a FunPtr value. Just pass it.
      res_d.arr = [[h$direct_sqlite.h$cstring(res_d.i3[0]),0]];
      if(ptr_d !== null) {
        ptr_d.arr = [[h$direct_sqlite.h$cstring(ptr_ptr),0]]
      }
      if(cb_ptr !== null) {
        h$direct_sqlite.removeFunction(cb_ptr);
      }
      return ret;
    });
  }
  // sqlite3_prepare_v2 :: Ptr CDatabase -> CString -> CNumBytes -> Ptr (Ptr CStatement) -> Ptr CString -> IO CError
  function h$sqlite3_prepare_v2(db_d, db_o, sql_d, sql_o, bytes, hdl_d, hdl_o, res_d, res_o) {
    return h$direct_sqlite.h$withCString(sql_d, sql_o, function(sql) {
      // console.log("prepare", h$direct_sqlite.h$debugHeapStr(sql));
      var hdl_ptr = h$direct_sqlite.h$getTmpBufferWith(1, hdl_d, hdl_o, 4);
          res_ptr = res_d === null ? null : h$direct_sqlite.h$getTmpBufferWith(2, res_d, res_o, 4);
      // console.log(sql_d, sql_o, sql);
      var ret = h$direct_sqlite._sqlite3_prepare_v2(db_d.i3[0], sql, bytes, hdl_ptr, res_ptr);
      var hdl_ptr_ = h$direct_sqlite.h$ptr(hdl_ptr);
      if(hdl_ptr_.i3[0] != 0) {
        hdl_d.arr = [[hdl_ptr_,0]];
      } else {
        hdl_d.arr = [null];
      }
      if(res_d !== null) {
        res_d.arr = [[h$direct_sqlite.h$cstring(res_ptr),0]];
      }
      return ret;
    });
  }
  // sqlite3_db_handle :: Ptr CStatement -> IO (Ptr CDatabase)
  function h$sqlite3_db_handle(stmt_d, stmt_o) {
    var ret = h$direct_sqlite._sqlite3_db_handle(stmt_d.i3[0]);
    var ptr = h$direct_sqlite.h$ptr(ret);
    ptr.arr = [[ptr, 0]];
    return ptr;
  }
  // sqlite3_step :: Ptr CStatement -> IO CError
  function h$sqlite3_step(stmt_d, stmt_o) {
    return h$direct_sqlite._sqlite3_step(stmt_d.i3[0]);
  }
  // sqlite3_step_unsafe :: Ptr CStatement -> IO CError
  function h$sqlite3_step_unsafe(stmt_d, stmt_o) {
    return h$direct_sqlite._sqlite3_step_unsafe(stmt_d.i3[0]);
  }
  // sqlite3_reset :: Ptr CStatement -> IO CError
  function h$sqlite3_reset(stmt_d, stmt_o) {
    return h$direct_sqlite._sqlite3_reset(stmt_d.i3[0]);
  }
  // sqlite3_finalize :: Ptr CStatement -> IO CError
  function h$sqlite3_finalize(stmt_d, stmt_o) {
    return h$direct_sqlite._sqlite3_finalize(stmt_d.i3[0]);
  }
  // sqlite3_clear_bindings :: Ptr CStatement -> IO CError
  function h$sqlite3_clear_bindings(stmt_d, stmt_o) {
    return h$direct_sqlite._sqlite3_clear_bindings(stmt_d.i3[0]);
  }
  // sqlite3_sql :: Ptr CStatement -> IO CString
  function h$sqlite3_sql(stmt_d, stmt_o) {
    h$ret1 = 0;
    return h$direct_sqlite.h$cstring(h$direct_sqlite._sqlite3_sql(stmt_d.i3[0]));
  }
  // sqlite3_bind_parameter_count :: Ptr CStatement -> IO CParamIndex
  function h$sqlite3_bind_parameter_count(stmt_d, stmt_o) {
    return h$direct_sqlite._sqlite3_bind_parameter_count(stmt_d.i3[0]);
  }

  // sqlite3_bind_parameter_name :: Ptr CStatement -> CParamIndex -> IO CString
  function h$sqlite3_bind_parameter_name(stmt_d, stmt_o, idx) {
    h$ret1 = 0; // this is the offset for the cstring!
    return h$direct_sqlite.h$cstring(h$direct_sqlite._sqlite3_bind_parameter_name(stmt_d.i3[0], idx));
  }
  // sqlite3_bind_parameter_index :: Ptr CStatement -> CString -> IO CParamIndex
  function h$sqlite3_bind_parameter_index(stmt_d, stmt_o, str_d, str_o) {
    return h$direct_sqlite.h$withCString(str_d, str_o, function (str) {
      return h$direct_sqlite._sqlite3_bind_parameter_index(stmt_d.i3[0], str);
    });
  }
  // sqlite3_column_count :: Ptr CStatement -> IO CColumnCount
  function h$sqlite3_column_count(stmt_d, stmt_o) {
    return h$direct_sqlite._sqlite3_column_count(stmt_d.i3[0]);
  }
  // sqlite3_column_name :: Ptr CStatement -> CColumnIndex -> IO CString
  function h$sqlite3_column_name(stmt_d, stmt_o, idx) {
    h$ret1 = 0;
    return h$direct_sqlite.h$cstring(h$direct_sqlite._sqlite3_column_name(stmt_d.i3[0], idx));
  }
  // sqlite3_bind_blob :: Ptr CStatement -> CParamIndex -> Ptr a -> CNumBytes -> Ptr CDestructor -> IO CError
  function h$sqlite3_bind_blob(stmt_d, stmt_o, idx, ptr_d, ptr_o, bytes, destr_d, destr_o) {
    return h$direct_sqlite.h$withCBuffer(ptr_d, ptr_o, bytes, function (blob) {
      return h$direct_sqlite._sqlite3_bind_blob(stmt_d.i3[0], idx, blob, bytes, destr_o);
    });
  }
  // sqlite3_bind_zeroblob :: Ptr CStatement -> CParamIndex -> CInt -> IO CError
  function h$sqlite3_bind_zeroblob(stmt_d, stmt_o, idx, n) {
    return h$direct_sqlite._sqlite3_bind_zeroblob(stmt_d.i3[0], idx, n);
  }``
  // sqlite3_bind_text :: Ptr CStatement -> CParamIndex -> CString -> CNumBytes -> Ptr CDestructor -> IO CError
  function h$sqlite3_bind_text(stmt_d, stmt_o, idx, str_d, str_o, bytes, destr_d, destr_o) {
    return h$direct_sqlite.h$withCBuffer(str_d, str_o, bytes, function(str) {
      // CDestructor is either (null, 0) for STATIC, or (null, -1) for TRANSIENT
      // we always free the string in the Emscripten heap right afterwards, so what
      // ever destructor is set, we are TRANSIENT in the emscripten heap!
      return h$direct_sqlite._sqlite3_bind_text(stmt_d.i3[0], idx, str, bytes, -1);
    });
  }
  // sqlite3_bind_double   :: Ptr CStatement -> CParamIndex -> Double -> IO CError
  function h$sqlite3_bind_double(stmt_d, stmt_o, idx, dbl) {
    return h$direct_sqlite._sqlite3_bind_double(stmt_d.i3[0], idx, dbl);
  }
  // sqlite3_bind_int64    :: Ptr CStatement -> CParamIndex -> Int64 -> IO CError
  function h$sqlite3_bind_int64(stmt_d, stmt_o, idx, val_msw, val_lsw) {
    return h$direct_sqlite._sqlite3_bind_int64(stmt_d.i3[0], idx, val_lsw, val_msw);
  }
  // sqlite3_bind_null     :: Ptr CStatement -> CParamIndex -> IO CError
  function h$sqlite3_bind_null(stmt_d, stmt_o, idx) {
    return h$direct_sqlite._sqlite3_bind_null(stmt_d.i3[0], idx);
  }
  // sqlite3_column_type   :: Ptr CStatement -> CColumnIndex -> IO CColumnType
  function h$sqlite3_column_type(stmt_d, stmt_o, idx) {
    return h$direct_sqlite._sqlite3_column_type(stmt_d.i3[0], idx);
  }
  // sqlite3_column_bytes  :: Ptr CStatement -> CColumnIndex -> IO CNumBytes
  function h$sqlite3_column_bytes(stmt_d, stmt_o, idx) {
    // console.log("column_bytes", idx);
    return h$direct_sqlite._sqlite3_column_bytes(stmt_d.i3[0], idx);
  }
  // sqlite3_column_blob   :: Ptr CStatement -> CColumnIndex -> IO (Ptr a)
  function h$sqlite3_column_blob(stmt_d, stmt_o, idx) {
    h$ret1 = h$direct_sqlite._sqlite3_column_blob(stmt_d.i3[0], idx);
    return { dv: new DataView(h$direct_sqlite.HEAPU8.buffer), u8: h$direct_sqlite.HEAPU8 };
  }
  // sqlite3_column_text   :: Ptr CStatement -> CColumnIndex -> IO CString
  function h$sqlite3_column_text(stmt_d, stmt_o, idx) {
    var ret = h$direct_sqlite._sqlite3_column_text(stmt_d.i3[0], idx);
    // console.log("column_text: ", h$direct_sqlite.h$debugHeapStr(ret));
    h$ret1 = ret;
    return { dv: new DataView(h$direct_sqlite.HEAPU8.buffer), u8: h$direct_sqlite.HEAPU8 };

    // ret = h$direct_sqlite.h$cstring(ret);
    // return
  }
  // sqlite3_column_int64  :: Ptr CStatement -> CColumnIndex -> IO Int64
  function h$sqlite3_column_int64(stmt_d, stmt_o, idx) {
    h$ret1 = h$direct_sqlite._sqlite3_column_int64(stmt_d.i3[0], idx);
    // console.log("column_int64: ", h$ret1, h$direct_sqlite.getTempRet0());
    return h$direct_sqlite.getTempRet0();
  }
  // sqlite3_column_double :: Ptr CStatement -> CColumnIndex -> IO Double
  function h$sqlite3_column_double(stmt_d, stmt_o, idx) {
    return h$direct_sqlite._sqlite3_column_double(stmt_d.i3[0], idx);
  }
  // sqlite3_last_insert_rowid :: Ptr CDatabase -> IO Int64
  function h$sqlite3_last_insert_rowid(stmt_d, stmt_o) {
    h$ret1 = h$direct_sqlite._sqlite3_last_insert_rowid(stmt_d.i3[0]);
    return h$direct_sqlite.getTempRet0();
  }
  // sqlite3_changes :: Ptr CDatabase -> IO CInt
  function h$sqlite3_changes(stmt_d, stmt_o) {
    return h$direct_sqlite._sqlite3_changes(stmt_d.i3[0]);
  }
  // sqlite3_total_changes :: Ptr CDatabase -> IO CInt
  function h$sqlite3_total_changes(stmt_d, stmt_o) {
    return h$direct_sqlite._sqlite3_total_changes(stmt_d.i3[0]);
  }
  // sqlite3_create_function_v2 :: Ptr CDatabase -> CString -> CArgCount -> CInt -> Ptr a -> FunPtr CFunc -> FunPtr CFunc -> FunPtr CFuncFinal -> FunPtr (CFuncDestroy a) -> IO CError
  function h$sqlite3_create_function_v2(db_d, db_o, name_d, name_o, nargs, enc, user_data_d, user_data_o, fun_buf, fun_sptr, step_buf, step_sptr, final_buf, final_sptr, destroy_buf, destroy_sptr) {
    var name = name_d === null ? null : h$direct_sqlite.h$copyStringToHeap(0, name_d, name_o);
        user_data = user_data_o; // so user_data is really a StablePtr; we'll just store the stablePtr offset.
        cb_fun = h$deRefStablePtr(fun_sptr);
        cb_step = h$deRefStablePtr(step_sptr);
        cb_final = h$deRefStablePtr(final_sptr);
        cb_destroy = h$deRefStablePtr(destroy_sptr);

        // Ptr CContext -> CArgCount -> Ptr (Ptr CValue) -> IO ()
        cb_fun_ = function(ctx_ptr, nargs, val_ptr) {
          // console.log("cb_fun", ctx_ptr, nargs, val_ptr);
          val_ptr_ = h$direct_sqlite.h$nptr(val_ptr, nargs);
          val_ptr_.arr = [];
          for(var i = 0; i < nargs; i++) {
            // we need to pad to 4 elements.
            var value = val_ptr_.i3[i] === 0 ? null : [val_ptr_.i3[i],0];
            val_ptr_.arr = val_ptr_.arr.concat([value, null, null, null]);
          }
          // console.log("Calling cb_fun...");
          ret = cb_fun([ctx_ptr,0], nargs, val_ptr_);
          // console.log("...called, with result", ret);
          return ret;
        };
        // Ptr CContext -> CArgCount -> Ptr (Ptr CValue) -> IO ()
        cb_step_ = function(ctx_ptr, nargs, val_ptr) {
          // console.log("step", ctx_ptr, nargs, val_ptr);
          val_ptr_ = h$direct_sqlite.h$nptr(val_ptr, nargs);
          val_ptr_.arr = [];
          for(var i = 0; i < nargs; i++) {
            // we need to pad to 4 elements.
            var value = val_ptr_.i3[i] === 0 ? null : [val_ptr_.i3[i],0];
            val_ptr_.arr = val_ptr_.arr.concat([value, null, null, null]);
          }
          return cb_step([ctx_ptr,0], nargs, val_ptr_);
        };
        // Ptr CContext -> IO ()
        cb_final_ = function(ctx_ptr) {
          // console.log("cb_final", ctx_ptr);
          return cb_final([ctx_ptr,0]);
        };
        // Ptr a -> IO ()
        cb_destroy_ = function(stbl_ptr) {
          // lucky we can close over user_data here.
          // console.log("cb_destroy: ", destroy_sptr, cb_destroy, h$deRefStablePtr(destroy_sptr));
          var cb_destroy = h$deRefStablePtr(destroy_sptr);
          return cb_destroy([user_data_d, user_data_o]);
        };
    cb_fun_ptr = cb_fun === null ? null : h$direct_sqlite.addFunction(cb_fun_);
    cb_step_ptr = cb_step === null ? null : h$direct_sqlite.addFunction(cb_step_);
    cb_final_ptr = cb_final === null ? null : h$direct_sqlite.addFunction(cb_final_);
    cb_destroy_ptr = cb_destroy === null ? null : h$direct_sqlite.addFunction(cb_destroy_);
    var res = h$direct_sqlite._sqlite3_create_function_v2(db_d.i3[0], name, nargs, enc, null, cb_fun_ptr, cb_step_ptr, cb_final_ptr, cb_destroy_ptr);
    if(cb_destroy_ptr != null) h$direct_sqlite.removeFunction(cb_destroy_ptr);
    if(cb_final_ptr != null) h$direct_sqlite.removeFunction(cb_final_ptr);
    if(cb_step_ptr != null) h$direct_sqlite.removeFunction(cb_step_ptr);
    if(cb_fun_ptr != null) h$direct_sqlite.removeFunction(cb_fun_ptr);
    return res;
  }
  // sqlite3_user_data :: Ptr CContext -> IO (Ptr a)
  // sqlite3_context_db_handle :: Ptr CContext -> IO (Ptr CDatabase)
  // sqlite3_aggregate_context :: Ptr CContext -> CNumBytes -> IO (Ptr a)
  function h$sqlite3_aggregate_context(ctx_d, ctx_o, nbytes) {
    // note, the [ctx_d, ctx_o], we obtain here are from the cb_step function
    // and are [<ptr value into the HEAPU8>, 0].
    h$ret1 = h$direct_sqlite._sqlite3_aggregate_context(ctx_d, nbytes);
    // console.log("aggregate_ctx", ctx_d, ctx_o, nbytes, "->", h$ret1);
    return { dv: new DataView(h$direct_sqlite.HEAPU8.buffer) };
  }
  // sqlite3_value_type   :: Ptr CValue -> IO CColumnType
  function h$sqlite3_value_type(val_d, val_o) {
    return h$direct_sqlite._sqlite3_value_type(val_d);
  }
  // sqlite3_value_bytes  :: Ptr CValue -> IO CNumBytes
  function h$sqlite3_value_bytes(val_d, val_o) {
    return h$direct_sqlite._sqlite3_value_bytes(val_d);
  }
  // sqlite3_value_blob   :: Ptr CValue -> IO (Ptr a)
  // sqlite3_value_text   :: Ptr CValue -> IO CString
  function h$sqlite3_value_text(val_d, val_o) {
    // console.log("value_text", val_d, val_o);
    h$ret1 = 0;
    return h$direct_sqlite.h$cstring(h$direct_sqlite._sqlite3_value_text(val_d));
  }
  // sqlite3_value_int64  :: Ptr CValue -> IO Int64
  function h$sqlite3_value_int64(val_d, val_o) {
    h$ret1 = h$direct_sqlite._sqlite3_value_int64(val_d);
    return h$direct_sqlite.getTempRet0();
  }
  // sqlite3_value_double :: Ptr CValue -> IO Double
  function h$sqlite3_value_double(val_d, val_o) {
    return h$direct_sqlite._sqlite3_value_double(val_d);
  }
  // sqlite3_result_null     :: Ptr CContext -> IO ()
  // sqlite3_result_blob     :: Ptr CContext -> Ptr a -> CNumBytes -> Ptr CDestructor -> IO ()
  // sqlite3_result_zeroblob :: Ptr CContext -> CNumBytes -> IO ()
  // sqlite3_result_text     :: Ptr CContext -> CString -> CNumBytes -> Ptr CDestructor -> IO ()
  function h$sqlite3_result_text(ctx_d, ctx_o, str_d, str_o, nbytes, destr_d, destr_o) {
    var str = h$direct_sqlite.h$getTmpBufferWith(0, str_d, str_o, nbytes);
    return h$direct_sqlite._sqlite3_result_text(ctx_d, str, nbytes, null);
  }
  // sqlite3_result_int64    :: Ptr CContext -> Int64 -> IO ()
  function h$sqlite3_result_int64(ctx_d, ctx_o, value_msw, value_lsw) {
    // console.log(ctx_d, ctx_o, value_msw, value_lsw);
    return h$direct_sqlite._sqlite3_result_int64(ctx_d, value_lsw, value_msw);
  }
  // sqlite3_result_double   :: Ptr CContext -> Double -> IO ()
  // sqlite3_result_value    :: Ptr CContext -> Ptr CValue -> IO ()
  // sqlite3_result_error    :: Ptr CContext -> CString -> CNumBytes -> IO ()
  function h$sqlite3_result_error(ctx_d, ctx_o, str_d, str_o, nbytes) {
    return h$direct_sqlite.h$withCBuffer(str_d, str_o, nbytes, function(str){
      // console.log("result_error", h$direct_sqlite.h$debugHeapStr(str), nbytes);
      return h$direct_sqlite._sqlite3_result_error(ctx_d, str, nbytes);
    });
  }
  // sqlite3_create_collation_v2 :: Ptr CDatabase
  //                             -> CString
  //                             -> CInt
  //                             -> Ptr a
  //                             -> FunPtr (CCompare a) -- Ptr a -> CNumBytes -> CString -> CNumBytes -> CString -> IO CInt
  //                             -> FunPtr (CFuncDestroy a) -- Ptr a -> IO ()
  //                             -> IO CError
  function h$sqlite3_create_collation_v2(db_d, db_o, name_d, name_o, flags, user_data_d, user_data_o, f_cmp_buf, f_cmp_sptr, f_destroy_buf, f_destroy_sptr) {
    // console.log("sqlite3_create_collation_v2", db_d, db_o, name_d, name_o, flags, user_data_d, user_data_o, f_cmp_buf, f_cmp_sptr, f_destroy_buf, f_destroy_sptr);
    return h$direct_sqlite.h$withCString(name_d, name_o, function(name) {
      // console.log("user data:", user_data_d, user_data_o, user_data_d === null ? 0 : user_data_d.len);
      // meh user_data is again some `castFunPtrToPtr`, so offset is probably some
      // offset into ???
      return h$direct_sqlite.h$withCBuffer(user_data_d, 0, user_data_d === null ? 0 : user_data_d.len, function(user_data) {
        return h$direct_sqlite.h$withFunction(f_cmp_sptr, function(f, user_data_ptr, len_a, str_a, len_b, str_b) {
          return f([user_data_d, user_data_o], len_a, [{ dv: new DataView(h$direct_sqlite.HEAPU8.buffer), u8: h$direct_sqlite.HEAPU8 }, str_a], len_b, [{ dv: new DataView(h$direct_sqlite.HEAPU8.buffer), u8: h$direct_sqlite.HEAPU8 }, str_b]);
        }, function(fcmp_ptr) {
          return h$direct_sqlite.h$withFunction(f_destroy_sptr, function (f, user_data_ptr) {
            return f([user_data_d, user_data_o]);
          }, function(fdestroy_ptr) {
            return h$direct_sqlite._sqlite3_create_collation_v2(db_d.i3[0], name, flags, user_data, fcmp_ptr, fdestroy_ptr);
          });
        });
      });
    });
  }
  // sqlite3_free :: Ptr a -> IO ()
  function h$sqlite3_free(ptr_d, ptr_o) {
    // console.log(ptr_d, ptr_o);
    return h$direct_sqlite._sqlite3_free(ptr_d.i3[0]);
  }
  // sqlite3_free_p :: FunPtr (Ptr a -> IO ())
  // sqlite3_enable_load_extension :: Ptr CDatabase -> Bool -> IO CError
  // sqlite3_wal_hook :: Ptr CDatabase -> FunPtr CWalHook -> Ptr a -> IO (Ptr ())
  // sqlite3_blob_open :: Ptr CDatabase -> CString -> CString -> CString -> Int64 -> CInt -> Ptr (Ptr CBlob) -> IO CError
  function h$sqlite3_blob_open(db_d, db_o, db_name_d, db_name_o, db_table_d, db_table_o, db_column_d, db_column_o, rowid_msw, rowid_lsw, flags, out_ptr_d, out_ptr_o) {
    var db_name = db_name_d === null ? null : h$direct_sqlite.h$copyStringToHeap(0, db_name_d, db_name_o);
        db_table = db_table_d === null ? null : h$direct_sqlite.h$copyStringToHeap(1, db_table_d, db_table_o);
        db_column = db_column_d === null ? null : h$direct_sqlite.h$copyStringToHeap(2, db_column_d, db_column_o);
        out_ptr = out_ptr_d === null ? null : h$direct_sqlite.h$getTmpBufferWith(3, out_ptr_d, out_ptr_o, 4);
    var ret = h$direct_sqlite._sqlite3_blob_open(db_d.i3[0], db_name, db_table, db_column, rowid_lsw, rowid_msw, flags, out_ptr);
    h$direct_sqlite.h$copyFromHeap(out_ptr, out_ptr_d, out_ptr_o, 4);
    out_ptr_d.arr = [[out_ptr_d.i3[0],0]];
    return ret;
  }
  // sqlite3_blob_close :: Ptr CBlob -> IO CError
  function h$sqlite3_blob_close(blob_d, blob_o) {
    return h$direct_sqlite._sqlite3_blob_close(blob_d);
  }
  // sqlite3_blob_reopen :: Ptr CBlob -> Int64 -> IO CError
  // sqlite3_blob_bytes :: Ptr CBlob -> IO CInt
  function h$sqlite3_blob_bytes(blob_d, blob_o) {
    return h$direct_sqlite._sqlite3_blob_bytes(blob_d);
  }
  // sqlite3_blob_read :: Ptr CBlob -> Ptr a -> CInt -> CInt -> IO CError
  function h$sqlite3_blob_read(blob_d, blob_o, out_ptr_d, out_ptr_o, nbytes, offset) {
    // console.log("blob_read", blob_d, out_ptr_d, out_ptr_o, nbytes, offset);
    var out_ptr = out_ptr_d === null ? null : h$direct_sqlite.h$getTmpBufferWith(0, out_ptr_d, out_ptr_o, nbytes);
    var ret = h$direct_sqlite._sqlite3_blob_read(blob_d, out_ptr, nbytes, offset);
    h$direct_sqlite.h$copyFromHeap(out_ptr, out_ptr_d, out_ptr_o, nbytes);
    return ret;
  }
  // sqlite3_blob_write :: Ptr CBlob -> Ptr a -> CInt -> CInt -> IO CError
  function h$sqlite3_blob_write(blob_d, blob_o, in_ptr_d, in_ptr_o, nbytes, offset) {
    return h$direct_sqlite.h$withCBuffer(in_ptr_d, in_ptr_o, nbytes, function(in_ptr) {
      // console.log("blob_write", blob_d, in_ptr, nbytes, offset);
      return h$direct_sqlite._sqlite3_blob_write(blob_d, in_ptr, nbytes, offset);
    });
  }
  // sqlite3_backup_init :: Ptr CDatabase -> CString -> Ptr CDatabase -> CString -> IO (Ptr CBackup)
  // sqlite3_backup_finish :: Ptr CBackup -> IO CError
  // sqlite3_backup_step :: Ptr CBackup -> CInt -> IO CError
  // sqlite3_backup_remaining :: Ptr CBackup -> IO CInt
  // sqlite3_backup_pagecount :: Ptr CBackup -> IO CInt
// Copyright 2011 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
