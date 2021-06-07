{-# LANGUAGE CPP #-}
{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}

module JavaScript.TypedArray.DataView.Internal where

import Data.Int
import Data.Typeable
import Data.Word

import GHC.Exts ( State# )

import GHCJS.Prim
import GHCJS.Internal.Types

import JavaScript.TypedArray.ArrayBuffer.Internal

newtype SomeDataView (a :: MutabilityType s) = SomeDataView JSVal
  deriving Typeable

type DataView        = SomeDataView Immutable
type MutableDataView = SomeDataView Mutable
type STDataView s    = SomeDataView (STMutable s)

#define JSU foreign import javascript unsafe
#define JSS foreign import javascript safe

JSU "new DataView($1)"
    js_dataView1 :: JSVal -> JSVal
JSS "new DataView($2,$1)"
    js_dataView2 :: Int -> JSVal -> SomeDataView m
JSU "new DataView($2,$1)"
    js_unsafeDataView2 :: Int -> JSVal-> SomeDataView m
JSS "new DataView($3,$1,$2)"
    js_dataView :: Int -> Int -> JSVal -> SomeDataView m
JSU "new DataView($3,$1,$2)" 
    js_unsafeDataView :: Int -> Int -> JSVal -> JSVal
JSU "new DataView($1.buffer.slice($1.byteOffset, $1.byteLength))"
    js_cloneDataView :: SomeDataView m -> IO (SomeDataView m1)

-- ----------------------------------------------------------------------------
-- immutable getters

JSU "$2.getInt8($1)"          js_i_unsafeGetInt8       :: Int -> DataView -> Int8
JSU "$2.getUint8($1)"         js_i_unsafeGetUint8      :: Int -> DataView -> Word8
JSU "$2.getInt16($1)"         js_i_unsafeGetInt16BE    :: Int -> DataView -> Int16
JSU "$2.getInt32($1)"         js_i_unsafeGetInt32BE    :: Int -> DataView -> Int
JSU "$2.getUint16($1)"        js_i_unsafeGetUint16BE   :: Int -> DataView -> Word16
JSU "$2.getUint32($1)|0"      js_i_unsafeGetUint32BE   :: Int -> DataView -> Word
JSU "$2.getFloat32($1)"       js_i_unsafeGetFloat32BE  :: Int -> DataView -> Double
JSU "$2.getFloat64($1)"       js_i_unsafeGetFloat64BE  :: Int -> DataView -> Double
JSU "$2.getInt16($1,true)"    js_i_unsafeGetInt16LE    :: Int -> DataView -> Int16
JSU "$2.getInt32($1,true)"    js_i_unsafeGetInt32LE    :: Int -> DataView -> Int
JSU "$2.getUint16($1,true)"   js_i_unsafeGetUint16LE   :: Int -> DataView -> Word16
JSU "$2.getUint32($1,true)|0" js_i_unsafeGetUint32LE   :: Int -> DataView -> Word
JSU "$2.getFloat32($1,true)"  js_i_unsafeGetFloat32LE  :: Int -> DataView -> Double
JSU "$2.getFloat64($1,true)"  js_i_unsafeGetFloat64LE  :: Int -> DataView -> Double

JSS "$2.getInt8($1)"          js_i_getInt8       :: Int -> DataView -> Int8
JSS "$2.getUint8($1)"         js_i_getUint8      :: Int -> DataView -> Word8
JSS "$2.getInt16($1)"         js_i_getInt16BE    :: Int -> DataView -> Int16
JSS "$2.getInt32($1)"         js_i_getInt32BE    :: Int -> DataView -> Int
JSS "$2.getUint16($1)"        js_i_getUint16BE   :: Int -> DataView -> Word16
JSS "$2.getUint32($1)|0"      js_i_getUint32BE   :: Int -> DataView -> Word
JSS "$2.getFloat32($1)"       js_i_getFloat32BE  :: Int -> DataView -> Double
JSS "$2.getFloat64($1)"       js_i_getFloat64BE  :: Int -> DataView -> Double
JSS "$2.getInt16($1,true)"    js_i_getInt16LE    :: Int -> DataView -> Int16
JSS "$2.getInt32($1,true)"    js_i_getInt32LE    :: Int -> DataView -> Int
JSS "$2.getUint16($1,true)"   js_i_getUint16LE   :: Int -> DataView -> Word16
JSS "$2.getUint32($1,true)|0" js_i_getUint32LE   :: Int -> DataView -> Word
JSS "$2.getFloat32($1,true)"  js_i_getFloat32LE  :: Int -> DataView -> Double
JSS "$2.getFloat64($1,true)"  js_i_getFloat64LE  :: Int -> DataView -> Double

-- ----------------------------------------------------------------------------
-- mutable getters

JSU "$2.getInt8($1)"          js_m_unsafeGetInt8      :: Int -> SomeDataView m -> State# s -> (# State# s, Int8   #)
JSU "$2.getUint8($1)"         js_m_unsafeGetUint8     :: Int -> SomeDataView m -> State# s -> (# State# s, Word8  #)
JSU "$2.getInt16($1)"         js_m_unsafeGetInt16BE   :: Int -> SomeDataView m -> State# s -> (# State# s, Int16  #)
JSU "$2.getInt32($1)"         js_m_unsafeGetInt32BE   :: Int -> SomeDataView m -> State# s -> (# State# s, Int    #)
JSU "$2.getUint16($1)"        js_m_unsafeGetUint16BE  :: Int -> SomeDataView m -> State# s -> (# State# s, Word16 #)
JSU "$2.getUint32($1)|0"      js_m_unsafeGetUint32BE  :: Int -> SomeDataView m -> State# s -> (# State# s, Word   #)
JSU "$2.getFloat32($1)"       js_m_unsafeGetFloat32BE :: Int -> SomeDataView m -> State# s -> (# State# s, Double #)
JSU "$2.getFloat64($1)"       js_m_unsafeGetFloat64BE :: Int -> SomeDataView m -> State# s -> (# State# s, Double #)
JSU "$2.getInt16($1,true)"    js_m_unsafeGetInt16LE   :: Int -> SomeDataView m -> State# s -> (# State# s, Int16  #)
JSU "$2.getInt32($1,true)"    js_m_unsafeGetInt32LE   :: Int -> SomeDataView m -> State# s -> (# State# s, Int    #)
JSU "$2.getUint16($1,true)"   js_m_unsafeGetUint16LE  :: Int -> SomeDataView m -> State# s -> (# State# s, Word16 #)
JSU "$2.getUint32($1,true)|0" js_m_unsafeGetUint32LE  :: Int -> SomeDataView m -> State# s -> (# State# s, Word   #)
JSU "$2.getFloat32($1,true)"  js_m_unsafeGetFloat32LE :: Int -> SomeDataView m -> State# s -> (# State# s, Double #)
JSU "$2.getFloat64($1,true)"  js_m_unsafeGetFloat64LE :: Int -> SomeDataView m -> State# s -> (# State# s, Double #)

JSS "$2.getInt8($1)"          js_m_getInt8            :: Int -> SomeDataView m -> State# s -> (# State# s, Int8   #)
JSS "$2.getUint8($1)"         js_m_getUint8           :: Int -> SomeDataView m -> State# s -> (# State# s, Word8  #)
JSS "$2.getInt16($1)"         js_m_getInt16BE         :: Int -> SomeDataView m -> State# s -> (# State# s, Int16  #)
JSS "$2.getInt32($1)"         js_m_getInt32BE         :: Int -> SomeDataView m -> State# s -> (# State# s, Int    #)
JSS "$2.getUint16($1)"        js_m_getUint16BE        :: Int -> SomeDataView m -> State# s -> (# State# s, Word16 #)
JSS "$2.getUint32($1)|0"      js_m_getUint32BE        :: Int -> SomeDataView m -> State# s -> (# State# s, Word   #)
JSS "$2.getFloat32($1)"       js_m_getFloat32BE       :: Int -> SomeDataView m -> State# s -> (# State# s, Double #)
JSS "$2.getFloat64($1)"       js_m_getFloat64BE       :: Int -> SomeDataView m -> State# s -> (# State# s, Double #)
JSS "$2.getInt16($1,true)"    js_m_getInt16LE         :: Int -> SomeDataView m -> State# s -> (# State# s, Int16  #)
JSS "$2.getInt32($1,true)"    js_m_getInt32LE         :: Int -> SomeDataView m -> State# s -> (# State# s, Int    #)
JSS "$2.getUint16($1,true)"   js_m_getUint16LE        :: Int -> SomeDataView m -> State# s -> (# State# s, Word16 #)
JSS "$2.getUint32($1,true)|0" js_m_getUint32LE        :: Int -> SomeDataView m -> State# s -> (# State# s, Word   #)
JSS "$2.getFloat32($1,true)"  js_m_getFloat32LE       :: Int -> SomeDataView m -> State# s -> (# State# s, Double #)
JSS "$2.getFloat64($1,true)"  js_m_getFloat64LE       :: Int -> SomeDataView m -> State# s -> (# State# s, Double #)

-- ----------------------------------------------------------------------------
-- mutable setters

JSU "$3.setInt8($1,$2)"         js_unsafeSetInt8      :: Int -> Int8   -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setUint8($1,$2)"        js_unsafeSetUint8     :: Int -> Word8  -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setInt16($1,$2)"        js_unsafeSetInt16BE   :: Int -> Int16  -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setInt32($1,$2)"        js_unsafeSetInt32BE   :: Int -> Int    -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setUint16($1,$2)"       js_unsafeSetUint16BE  :: Int -> Word16 -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setUint32($1,$2)"       js_unsafeSetUint32BE  :: Int -> Word   -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setFloat32($1,$2)"      js_unsafeSetFloat32BE :: Int -> Double -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setFloat64($1,$2)"      js_unsafeSetFloat64BE :: Int -> Double -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setInt16($1,$2,true)"   js_unsafeSetInt16LE   :: Int -> Int16  -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setInt32($1,$2,true)"   js_unsafeSetInt32LE   :: Int -> Int    -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setUint16($1,$2,true)"  js_unsafeSetUint16LE  :: Int -> Word16 -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setUint32($1,$2,true)"  js_unsafeSetUint32LE  :: Int -> Word   -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setFloat32($1,$2,true)" js_unsafeSetFloat32LE :: Int -> Double -> SomeDataView m -> State# s -> (# State# s, () #)
JSU "$3.setFloat64($1,$2,true)" js_unsafeSetFloat64LE :: Int -> Double -> SomeDataView m -> State# s -> (# State# s, () #)

JSS "$3.setInt8($1,$2)"         js_setInt8            :: Int -> Int8   -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setUint8($1,$2)"        js_setUint8           :: Int -> Word8  -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setInt16($1,$2)"        js_setInt16BE         :: Int -> Int16  -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setInt32($1,$2)"        js_setInt32BE         :: Int -> Int    -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setUint16($1,$2)"       js_setUint16BE        :: Int -> Word16 -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setUint32($1,$2)"       js_setUint32BE        :: Int -> Word   -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setFloat32($1,$2)"      js_setFloat32BE       :: Int -> Double -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setFloat64($1,$2)"      js_setFloat64BE       :: Int -> Double -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setInt16($1,$2,true)"   js_setInt16LE         :: Int -> Int16  -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setInt32($1,$2,true)"   js_setInt32LE         :: Int -> Int    -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setUint16($1,$2,true)"  js_setUint16LE        :: Int -> Word16 -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setUint32($1,$2,true)"  js_setUint32LE        :: Int -> Word   -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setFloat32($1,$2,true)" js_setFloat32LE       :: Int -> Double -> SomeDataView m -> State# s -> (# State# s, () #)
JSS "$3.setFloat64($1,$2,true)" js_setFloat64LE       :: Int -> Double -> SomeDataView m -> State# s -> (# State# s, () #)

