module JavaScript.TypedArray.DataView.ST
    ( STDataView
    , dataView
    , freeze, unsafeFreeze
    , thaw, unsafeThaw
      -- * reading
    , readInt8,                       unsafeReadInt8
    , readInt16LE,    readInt16BE,    unsafeReadInt16LE,    unsafeReadInt16BE
    , readInt32LE,    readInt32BE,    unsafeReadInt32LE,    unsafeReadInt32BE
    , readUint8,                      unsafeReadUint8
    , readUint16LE,   readUint16BE,   unsafeReadUint16LE,   unsafeReadUint16BE
    , readUint32LE,   readUint32BE,   unsafeReadUint32LE,   unsafeReadUint32BE
    , readFloat32LE,  readFloat32BE,  unsafeReadFloat32LE,  unsafeReadFloat32BE
    , readFloat64LE,  readFloat64BE,  unsafeReadFloat64LE,  unsafeReadFloat64BE
      -- * writing
    , writeInt8,                      unsafeWriteInt8
    , writeInt16LE,   writeInt16BE,   unsafeWriteInt16LE,   unsafeWriteInt16BE
    , writeInt32LE,   writeInt32BE,   unsafeWriteInt32LE,   unsafeWriteInt32BE
    , writeUint8,                     unsafeWriteUint8
    , writeUint16LE,  writeUint16BE,  unsafeWriteUint16LE,  unsafeWriteUint16BE
    , writeUint32LE,  writeUint32BE,  unsafeWriteUint32LE,  unsafeWriteUint32BE
    , writeFloat32LE, writeFloat32BE, unsafeWriteFloat32LE, unsafeWriteFloat32BE
    , writeFloat64LE, writeFloat64BE, unsafeWriteFloat64LE, unsafeWriteFloat64BE
    ) where

import Data.Int
import Data.Word

import GHC.ST

import GHCJS.Prim

import           JavaScript.TypedArray.ArrayBuffer.ST
import           JavaScript.TypedArray.ArrayBuffer.Internal as AI
import           JavaScript.TypedArray.DataView.Internal ( SomeDataView(..), STDataView )
import qualified JavaScript.TypedArray.DataView.Internal as I


{- | Create a 'DataView' for the whole 'ArrayBuffer' -}
dataView :: STArrayBuffer s -> STDataView s
dataView (SomeArrayBuffer b) = SomeDataView (I.js_dataView1 b)
{-# INLINE dataView #-}

{- | Create a 'STDataView' for part of an 'STArrayBuffer'
     Throws a `JSException' if the range specified by the
     offset and length exceeds the size of the buffer
 -}
dataView' :: Int             -- ^ start in bytes
          -> Maybe Int       -- ^ length in bytes, remainder of buffer if 'Nothing'
          -> STArrayBuffer s -- ^ buffer to view
          -> STDataView s
dataView' byteOffset mbyteLength (SomeArrayBuffer b) =
  case mbyteLength of
    Nothing         -> I.js_dataView2 byteOffset b
    Just byteLength -> I.js_dataView byteOffset byteLength b
{-# INLINE dataView' #-}

{- | Create an 'STDataView' for part of an 'STArrayBuffer'.
     If the range specified by the offset and length exceeds the size
     off the buffer, the resulting exception from the underlying call
     kills the Haskell thread.
 -}
unsafeDataView' :: Int             -- ^ start in bytes
                -> Maybe Int       -- ^ length in bytes, remainder of buffer if 'Nothing'
                -> STArrayBuffer s -- ^ buffer to view
                -> STDataView s
unsafeDataView' byteOffset mbyteLength (SomeArrayBuffer b) =
  case mbyteLength of
    Nothing         -> I.js_dataView2 byteOffset b
    Just byteLength -> I.js_dataView byteOffset byteLength b
{-# INLINE unsafeDataView' #-}

-- ----------------------------------------------------------------------------
-- mutable getters

readInt8, unsafeReadInt8 :: Int -> STDataView s -> ST s Int8
readInt8       idx dv = ST (I.js_m_getInt8       idx dv)
unsafeReadInt8 idx dv = ST (I.js_m_unsafeGetInt8 idx dv)
{-# INLINE readInt8 #-}

readUint8, unsafeReadUint8 :: Int -> STDataView s -> ST s Word8
readUint8       idx dv = ST (I.js_m_unsafeGetUint8 idx dv)
unsafeReadUint8 idx dv = ST (I.js_m_unsafeGetUint8 idx dv)
{-# INLINE readUint8 #-}

readInt16LE, readInt16BE, unsafeReadInt16LE, unsafeReadInt16BE
  :: Int -> STDataView s -> ST s Int16
readInt16LE       idx dv = ST (I.js_m_getInt16LE       idx dv)
readInt16BE       idx dv = ST (I.js_m_getInt16BE       idx dv)
unsafeReadInt16LE idx dv = ST (I.js_m_unsafeGetInt16LE idx dv)
unsafeReadInt16BE idx dv = ST (I.js_m_unsafeGetInt16BE idx dv)
{-# INLINE readInt16LE #-}
{-# INLINE readInt16BE #-}
{-# INLINE unsafeReadInt16LE #-}
{-# INLINE unsafeReadInt16BE #-}

readUint16LE, readUint16BE, unsafeReadUint16LE, unsafeReadUint16BE
  :: Int -> STDataView s -> ST s Word16
readUint16LE       idx dv = ST (I.js_m_getUint16LE       idx dv)
readUint16BE       idx dv = ST (I.js_m_getUint16BE       idx dv)
unsafeReadUint16LE idx dv = ST (I.js_m_unsafeGetUint16LE idx dv)
unsafeReadUint16BE idx dv = ST (I.js_m_unsafeGetUint16BE idx dv)
{-# INLINE readUint16LE #-}
{-# INLINE readUint16BE #-}
{-# INLINE unsafeReadUint16LE #-}
{-# INLINE unsafeReadUint16BE #-}

readInt32LE, readInt32BE, unsafeReadInt32LE, unsafeReadInt32BE
  :: Int -> STDataView s -> ST s Int
readInt32LE       idx dv = ST (I.js_m_getInt32LE       idx dv)
readInt32BE       idx dv = ST (I.js_m_getInt32BE       idx dv)
unsafeReadInt32LE idx dv = ST (I.js_m_unsafeGetInt32LE idx dv)
unsafeReadInt32BE idx dv = ST (I.js_m_unsafeGetInt32BE idx dv)
{-# INLINE readInt32LE #-}
{-# INLINE readInt32BE #-}
{-# INLINE unsafeReadInt32LE #-}
{-# INLINE unsafeReadInt32BE #-}

readUint32LE, readUint32BE, unsafeReadUint32LE, unsafeReadUint32BE
  :: Int -> STDataView s -> ST s Word
readUint32LE       idx dv = ST (I.js_m_getUint32LE       idx dv)
readUint32BE       idx dv = ST (I.js_m_getUint32BE       idx dv)
unsafeReadUint32LE idx dv = ST (I.js_m_unsafeGetUint32LE idx dv)
unsafeReadUint32BE idx dv = ST (I.js_m_unsafeGetUint32BE idx dv)
{-# INLINE readUint32LE #-}
{-# INLINE readUint32BE #-}
{-# INLINE unsafeReadUint32LE #-}
{-# INLINE unsafeReadUint32BE #-}

readFloat32LE, readFloat32BE, unsafeReadFloat32LE, unsafeReadFloat32BE
  :: Int -> STDataView s -> ST s Double
readFloat32LE       idx dv = ST (I.js_m_getFloat32LE       idx dv)
readFloat32BE       idx dv = ST (I.js_m_getFloat32BE       idx dv)
unsafeReadFloat32LE idx dv = ST (I.js_m_unsafeGetFloat32LE idx dv)
unsafeReadFloat32BE idx dv = ST (I.js_m_unsafeGetFloat32BE idx dv)
{-# INLINE readFloat32LE #-}
{-# INLINE readFloat32BE #-}
{-# INLINE unsafeReadFloat32LE #-}
{-# INLINE unsafeReadFloat32BE #-}

readFloat64LE, readFloat64BE, unsafeReadFloat64LE, unsafeReadFloat64BE
  :: Int -> STDataView s -> ST s Double
readFloat64LE       idx dv = ST (I.js_m_getFloat64LE       idx dv)
readFloat64BE       idx dv = ST (I.js_m_getFloat64BE       idx dv)
unsafeReadFloat64LE idx dv = ST (I.js_m_unsafeGetFloat64LE idx dv)
unsafeReadFloat64BE idx dv = ST (I.js_m_unsafeGetFloat64BE idx dv)
{-# INLINE readFloat64LE #-}
{-# INLINE readFloat64BE #-}
{-# INLINE unsafeReadFloat64LE #-}
{-# INLINE unsafeReadFloat64BE #-}

-- ----------------------------------------------------------------------------
-- mutable setters

writeInt8, unsafeWriteInt8 :: Int -> Int8 -> STDataView s -> ST s ()
writeInt8       idx x dv = ST (I.js_setInt8       idx x dv)
unsafeWriteInt8 idx x dv = ST (I.js_unsafeSetInt8 idx x dv)
{-# INLINE writeInt8 #-}
{-# INLINE unsafeWriteInt8 #-}

writeUint8, unsafeWriteUint8 :: Int -> Word8 -> STDataView s -> ST s ()
writeUint8       idx x dv = ST (I.js_setUint8       idx x dv)
unsafeWriteUint8 idx x dv = ST (I.js_unsafeSetUint8 idx x dv)
{-# INLINE writeUint8 #-}
{-# INLINE unsafeWriteUint8 #-}

writeInt16LE, writeInt16BE, unsafeWriteInt16LE, unsafeWriteInt16BE
  :: Int -> Int16 -> STDataView s -> ST s ()
writeInt16LE       idx x dv = ST (I.js_setInt16LE       idx x dv)
writeInt16BE       idx x dv = ST (I.js_setInt16BE       idx x dv)
unsafeWriteInt16LE idx x dv = ST (I.js_unsafeSetInt16LE idx x dv)
unsafeWriteInt16BE idx x dv = ST (I.js_unsafeSetInt16BE idx x dv)
{-# INLINE writeInt16LE #-}
{-# INLINE writeInt16BE #-}
{-# INLINE unsafeWriteInt16LE #-}
{-# INLINE unsafeWriteInt16BE #-}

writeUint16LE, writeUint16BE, unsafeWriteUint16LE, unsafeWriteUint16BE
  :: Int -> Word16 -> STDataView s -> ST s ()
writeUint16LE       idx x dv = ST (I.js_setUint16LE       idx x dv)
writeUint16BE       idx x dv = ST (I.js_setUint16BE       idx x dv)
unsafeWriteUint16LE idx x dv = ST (I.js_unsafeSetUint16LE idx x dv)
unsafeWriteUint16BE idx x dv = ST (I.js_unsafeSetUint16BE idx x dv)
{-# INLINE writeUint16LE #-}
{-# INLINE writeUint16BE #-}
{-# INLINE unsafeWriteUint16LE #-}
{-# INLINE unsafeWriteUint16BE #-}

writeInt32LE, writeInt32BE, unsafeWriteInt32LE, unsafeWriteInt32BE
  :: Int -> Int -> STDataView s -> ST s ()
writeInt32LE       idx x dv = ST (I.js_setInt32LE       idx x dv)
writeInt32BE       idx x dv = ST (I.js_setInt32BE       idx x dv)
unsafeWriteInt32LE idx x dv = ST (I.js_unsafeSetInt32LE idx x dv)
unsafeWriteInt32BE idx x dv = ST (I.js_unsafeSetInt32BE idx x dv)
{-# INLINE writeInt32LE #-}
{-# INLINE writeInt32BE #-}
{-# INLINE unsafeWriteInt32LE #-}
{-# INLINE unsafeWriteInt32BE #-}

writeUint32LE, writeUint32BE, unsafeWriteUint32LE, unsafeWriteUint32BE
  :: Int -> Word -> STDataView s -> ST s ()
writeUint32LE       idx x dv = ST (I.js_setUint32LE       idx x dv)
writeUint32BE       idx x dv = ST (I.js_setUint32BE       idx x dv)
unsafeWriteUint32LE idx x dv = ST (I.js_unsafeSetUint32LE idx x dv)
unsafeWriteUint32BE idx x dv = ST (I.js_unsafeSetUint32BE idx x dv)
{-# INLINE writeUint32LE #-}
{-# INLINE writeUint32BE #-}
{-# INLINE unsafeWriteUint32LE #-}
{-# INLINE unsafeWriteUint32BE #-}

writeFloat32LE, writeFloat32BE, unsafeWriteFloat32LE, unsafeWriteFloat32BE
  :: Int -> Double -> STDataView s -> ST s ()
writeFloat32LE       idx x dv = ST (I.js_setFloat32LE       idx x dv)
writeFloat32BE       idx x dv = ST (I.js_setFloat32BE       idx x dv)
unsafeWriteFloat32LE idx x dv = ST (I.js_unsafeSetFloat32LE idx x dv)
unsafeWriteFloat32BE idx x dv = ST (I.js_unsafeSetFloat32BE idx x dv)
{-# INLINE writeFloat32LE #-}
{-# INLINE writeFloat32BE #-}
{-# INLINE unsafeWriteFloat32LE #-}
{-# INLINE unsafeWriteFloat32BE #-}

writeFloat64LE, writeFloat64BE, unsafeWriteFloat64LE, unsafeWriteFloat64BE
  :: Int -> Double -> STDataView s -> ST s ()
writeFloat64LE       idx x dv = ST (I.js_setFloat64LE       idx x dv)
writeFloat64BE       idx x dv = ST (I.js_setFloat64BE       idx x dv)
unsafeWriteFloat64LE idx x dv = ST (I.js_unsafeSetFloat64LE idx x dv)
unsafeWriteFloat64BE idx x dv = ST (I.js_unsafeSetFloat64BE idx x dv)
{-# INLINE writeFloat64LE #-}
{-# INLINE writeFloat64BE #-}
{-# INLINE unsafeWriteFloat64LE #-}
{-# INLINE unsafeWriteFloat64BE #-}

