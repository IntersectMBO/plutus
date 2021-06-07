{-# LANGUAGE CPP #-}
module JavaScript.TypedArray.DataView
    ( DataView
    , MutableDataView
    , dataView
--    , mutableDataView
    , freeze, unsafeFreeze
    , thaw, unsafeThaw
      -- * reading an immutable dataview
    , getInt8,                        unsafeGetInt8
    , getInt16LE,     getInt16BE,     unsafeGetInt16LE,     unsafeGetInt16BE
    , getInt32LE,     getInt32BE,     unsafeGetInt32LE,     unsafeGetInt32BE
    , getUint8,                       unsafeGetUint8
    , getUint16LE,    getUint16BE,    unsafeGetUint16LE,    unsafeGetUint16BE
    , getUint32LE,    getUint32BE,    unsafeGetUint32LE,    unsafeGetUint32BE
    , getFloat32LE,   getFloat32BE,   unsafeGetFloat32LE,   unsafeGetFloat32BE
    , getFloat64LE,   getFloat64BE,   unsafeGetFloat64LE,   unsafeGetFloat64BE
      -- * reading a mutable dataview
    , readInt8,                       unsafeReadInt8
    , readInt16LE,    readInt16BE,    unsafeReadInt16LE,    unsafeReadInt16BE
    , readInt32LE,    readInt32BE,    unsafeReadInt32LE,    unsafeReadInt32BE
    , readUint8,                      unsafeReadUint8
    , readUint16LE,   readUint16BE,   unsafeReadUint16LE,   unsafeReadUint16BE
    , readUint32LE,   readUint32BE,   unsafeReadUint32LE,   unsafeReadUint32BE
    , readFloat32LE,  readFloat32BE,  unsafeReadFloat32LE,  unsafeReadFloat32BE
    , readFloat64LE,  readFloat64BE,  unsafeReadFloat64LE,  unsafeReadFloat64BE
      -- * writing to a mutable dataview
    , writeInt8,                      unsafeWriteInt8
    , writeInt16LE,   writeInt16BE,   unsafeWriteInt16LE,   unsafeWriteInt16BE
    , writeInt32LE,   writeInt32BE,   unsafeWriteInt32LE,   unsafeWriteInt32BE
    , writeUint8,                     unsafeWriteUint8
    , writeUint16LE,  writeUint16BE,  unsafeWriteUint16LE,  unsafeWriteUint16BE
    , writeUint32LE,  writeUint32BE,  unsafeWriteUint32LE,  unsafeWriteUint32BE
    , writeFloat32LE, writeFloat32BE, unsafeWriteFloat32LE, unsafeWriteFloat32BE
    , writeFloat64LE, writeFloat64BE, unsafeWriteFloat64LE, unsafeWriteFloat64BE
    ) where

import GHC.Types (IO(..))

import Data.Int
import Data.Word

import GHCJS.Prim

import           JavaScript.TypedArray.ArrayBuffer.Internal
  ( SomeArrayBuffer(..), ArrayBuffer, MutableArrayBuffer )
import qualified JavaScript.TypedArray.ArrayBuffer       as A
import           JavaScript.TypedArray.DataView.Internal
  ( SomeDataView(..), DataView, MutableDataView )
import qualified JavaScript.TypedArray.DataView.Internal as I

{- | Create a 'DataView' for the whole 'ArrayBuffer' -}
dataView :: SomeArrayBuffer any -> SomeDataView any
dataView (SomeArrayBuffer b) = SomeDataView (I.js_dataView1 b)
{-# INLINE dataView #-}

{- | Create a 'DataView' for part of an 'ArrayBuffer'
     Throws a `JSException' if the range specified by the
     offset and length exceeds the size of the buffer
 -}
dataView' :: Int                 -- ^ start in bytes
          -> Maybe Int           -- ^ length in bytes, remainder of buffer if 'Nothing'
          -> SomeArrayBuffer any -- ^ buffer to view
          -> SomeDataView any
dataView' byteOffset mbyteLength (SomeArrayBuffer b) =
  case mbyteLength of
    Nothing         -> I.js_dataView2 byteOffset b
    Just byteLength -> I.js_dataView byteOffset byteLength b
{-# INLINE dataView' #-}

{- | Create a 'DataView' for part of an 'ArrayBuffer'.
     If the range specified by the offset and length exceeds the size
     off the buffer, the resulting exception from the underlying call
     kills the Haskell thread.
 -}
unsafeDataView' :: Int                 -- ^ start in bytes
                -> Maybe Int           -- ^ length in bytes, remainder of buffer if 'Nothing'
                -> SomeArrayBuffer any -- ^ buffer to view
                -> SomeDataView any
unsafeDataView' byteOffset mbyteLength (SomeArrayBuffer b) =
  case mbyteLength of
    Nothing         -> I.js_dataView2 byteOffset b
    Just byteLength -> I.js_dataView byteOffset byteLength b
{-# INLINE unsafeDataView' #-}

thaw :: DataView -> IO MutableDataView
thaw d = I.js_cloneDataView d
{-# INLINE thaw #-}

unsafeThaw :: DataView -> IO MutableDataView
unsafeThaw (SomeDataView d) = return (SomeDataView d)
{-# INLINE unsafeThaw #-}

freeze :: MutableDataView -> IO DataView
freeze d = I.js_cloneDataView d
{-# INLINE freeze #-}

unsafeFreeze :: MutableDataView -> IO DataView
unsafeFreeze (SomeDataView d) = return (SomeDataView d)
{-# INLINE unsafeFreeze #-}

-- ----------------------------------------------------------------------------
-- immutable getters

getInt8, unsafeGetInt8 :: Int -> DataView -> Int8
getInt8       idx dv = I.js_i_getInt8       idx dv
unsafeGetInt8 idx dv = I.js_i_unsafeGetInt8 idx dv
{-# INLINE getInt8 #-}

getUint8, unsafeGetUint8 :: Int -> DataView -> Word8
getUint8       idx dv = I.js_i_getUint8       idx dv
unsafeGetUint8 idx dv = I.js_i_unsafeGetUint8 idx dv
{-# INLINE getUint8 #-}

getInt16LE, getInt16BE, unsafeGetInt16LE, unsafeGetInt16BE
  :: Int -> DataView -> Int16
getInt16LE       idx dv = I.js_i_getInt16LE       idx dv
getInt16BE       idx dv = I.js_i_getInt16BE       idx dv
unsafeGetInt16LE idx dv = I.js_i_unsafeGetInt16LE idx dv
unsafeGetInt16BE idx dv = I.js_i_unsafeGetInt16BE idx dv
{-# INLINE getInt16LE #-}
{-# INLINE getInt16BE #-}
{-# INLINE unsafeGetInt16LE #-}
{-# INLINE unsafeGetInt16BE #-}

getUint16LE, getUint16BE, unsafeGetUint16LE, unsafeGetUint16BE
  :: Int -> DataView -> Word16
getUint16LE       idx dv = I.js_i_getUint16LE       idx dv
getUint16BE       idx dv = I.js_i_getUint16BE       idx dv
unsafeGetUint16LE idx dv = I.js_i_unsafeGetUint16LE idx dv
unsafeGetUint16BE idx dv = I.js_i_unsafeGetUint16BE idx dv
{-# INLINE getUint16LE #-}
{-# INLINE getUint16BE #-}
{-# INLINE unsafeGetUint16LE #-}
{-# INLINE unsafeGetUint16BE #-}

getInt32LE, getInt32BE, unsafeGetInt32LE, unsafeGetInt32BE
  :: Int -> DataView -> Int
getInt32LE       idx dv = I.js_i_getInt32LE       idx dv
getInt32BE       idx dv = I.js_i_getInt32BE       idx dv
unsafeGetInt32LE idx dv = I.js_i_unsafeGetInt32LE idx dv
unsafeGetInt32BE idx dv = I.js_i_unsafeGetInt32BE idx dv
{-# INLINE getInt32LE #-}
{-# INLINE getInt32BE #-}
{-# INLINE unsafeGetInt32LE #-}
{-# INLINE unsafeGetInt32BE #-}

getUint32LE, getUint32BE, unsafeGetUint32LE, unsafeGetUint32BE
  :: Int -> DataView -> Word
getUint32LE       idx dv = I.js_i_getUint32LE       idx dv
getUint32BE       idx dv = I.js_i_getUint32BE       idx dv
unsafeGetUint32LE idx dv = I.js_i_unsafeGetUint32LE idx dv
unsafeGetUint32BE idx dv = I.js_i_unsafeGetUint32BE idx dv
{-# INLINE getUint32LE #-}
{-# INLINE getUint32BE #-}
{-# INLINE unsafeGetUint32LE #-}
{-# INLINE unsafeGetUint32BE #-}

getFloat32LE, getFloat32BE, unsafeGetFloat32LE, unsafeGetFloat32BE
  :: Int -> DataView -> Double
getFloat32LE       idx dv = I.js_i_getFloat32LE       idx dv
getFloat32BE       idx dv = I.js_i_getFloat32BE       idx dv
unsafeGetFloat32LE idx dv = I.js_i_unsafeGetFloat32LE idx dv
unsafeGetFloat32BE idx dv = I.js_i_unsafeGetFloat32BE idx dv
{-# INLINE getFloat32LE #-}
{-# INLINE getFloat32BE #-}
{-# INLINE unsafeGetFloat32LE #-}
{-# INLINE unsafeGetFloat32BE #-}

getFloat64LE, getFloat64BE, unsafeGetFloat64LE, unsafeGetFloat64BE
  :: Int -> DataView -> Double
getFloat64LE       idx dv = I.js_i_getFloat64LE       idx dv
getFloat64BE       idx dv = I.js_i_getFloat64BE       idx dv
unsafeGetFloat64LE idx dv = I.js_i_unsafeGetFloat64LE idx dv
unsafeGetFloat64BE idx dv = I.js_i_unsafeGetFloat64BE idx dv
{-# INLINE getFloat64LE #-}
{-# INLINE getFloat64BE #-}
{-# INLINE unsafeGetFloat64LE #-}
{-# INLINE unsafeGetFloat64BE #-}

-- ----------------------------------------------------------------------------
-- mutable getters

readInt8, unsafeReadInt8 :: Int -> MutableDataView -> IO Int8
readInt8       idx dv = IO (I.js_m_getInt8       idx dv)
unsafeReadInt8 idx dv = IO (I.js_m_unsafeGetInt8 idx dv)
{-# INLINE readInt8 #-}

readUint8, unsafeReadUint8 :: Int -> MutableDataView -> IO Word8
readUint8       idx dv = IO (I.js_m_getUint8       idx dv)
unsafeReadUint8 idx dv = IO (I.js_m_unsafeGetUint8 idx dv)
{-# INLINE readUint8 #-}

readInt16LE, readInt16BE, unsafeReadInt16LE, unsafeReadInt16BE
  :: Int -> MutableDataView -> IO Int16
readInt16LE       idx dv = IO (I.js_m_getInt16LE       idx dv)
readInt16BE       idx dv = IO (I.js_m_getInt16BE       idx dv)
unsafeReadInt16LE idx dv = IO (I.js_m_unsafeGetInt16LE idx dv)
unsafeReadInt16BE idx dv = IO (I.js_m_unsafeGetInt16BE idx dv)
{-# INLINE readInt16LE #-}
{-# INLINE readInt16BE #-}
{-# INLINE unsafeReadInt16LE #-}
{-# INLINE unsafeReadInt16BE #-}

readUint16LE, readUint16BE, unsafeReadUint16LE, unsafeReadUint16BE
  :: Int -> MutableDataView -> IO Word16
readUint16LE       idx dv = IO (I.js_m_getUint16LE       idx dv)
readUint16BE       idx dv = IO (I.js_m_getUint16BE       idx dv)
unsafeReadUint16LE idx dv = IO (I.js_m_unsafeGetUint16LE idx dv)
unsafeReadUint16BE idx dv = IO (I.js_m_unsafeGetUint16BE idx dv)
{-# INLINE readUint16LE #-}
{-# INLINE readUint16BE #-}
{-# INLINE unsafeReadUint16LE #-}
{-# INLINE unsafeReadUint16BE #-}

readInt32LE, readInt32BE, unsafeReadInt32LE, unsafeReadInt32BE
  :: Int -> MutableDataView -> IO Int
readInt32LE       idx dv = IO (I.js_m_getInt32LE       idx dv)
readInt32BE       idx dv = IO (I.js_m_getInt32BE       idx dv)
unsafeReadInt32LE idx dv = IO (I.js_m_unsafeGetInt32LE idx dv)
unsafeReadInt32BE idx dv = IO (I.js_m_unsafeGetInt32BE idx dv)
{-# INLINE readInt32LE #-}
{-# INLINE readInt32BE #-}
{-# INLINE unsafeReadInt32LE #-}
{-# INLINE unsafeReadInt32BE #-}

readUint32LE, readUint32BE, unsafeReadUint32LE, unsafeReadUint32BE
  :: Int -> MutableDataView -> IO Word
readUint32LE       idx dv = IO (I.js_m_getUint32LE       idx dv)
readUint32BE       idx dv = IO (I.js_m_getUint32BE       idx dv)
unsafeReadUint32LE idx dv = IO (I.js_m_unsafeGetUint32LE idx dv)
unsafeReadUint32BE idx dv = IO (I.js_m_unsafeGetUint32BE idx dv)
{-# INLINE readUint32LE #-}
{-# INLINE readUint32BE #-}
{-# INLINE unsafeReadUint32LE #-}
{-# INLINE unsafeReadUint32BE #-}

readFloat32LE, readFloat32BE, unsafeReadFloat32LE, unsafeReadFloat32BE
  :: Int -> MutableDataView -> IO Double
readFloat32LE       idx dv = IO (I.js_m_getFloat32LE       idx dv)
readFloat32BE       idx dv = IO (I.js_m_getFloat32BE       idx dv)
unsafeReadFloat32LE idx dv = IO (I.js_m_unsafeGetFloat32LE idx dv)
unsafeReadFloat32BE idx dv = IO (I.js_m_unsafeGetFloat32BE idx dv)
{-# INLINE readFloat32LE #-}
{-# INLINE readFloat32BE #-}
{-# INLINE unsafeReadFloat32LE #-}
{-# INLINE unsafeReadFloat32BE #-}

readFloat64LE, readFloat64BE, unsafeReadFloat64LE, unsafeReadFloat64BE
  :: Int -> MutableDataView -> IO Double
readFloat64LE       idx dv = IO (I.js_m_getFloat64LE       idx dv)
readFloat64BE       idx dv = IO (I.js_m_getFloat64BE       idx dv)
unsafeReadFloat64LE idx dv = IO (I.js_m_unsafeGetFloat64LE idx dv)
unsafeReadFloat64BE idx dv = IO (I.js_m_unsafeGetFloat64BE idx dv)
{-# INLINE readFloat64LE #-}
{-# INLINE readFloat64BE #-}
{-# INLINE unsafeReadFloat64LE #-}
{-# INLINE unsafeReadFloat64BE #-}

-- ----------------------------------------------------------------------------
-- mutable setters

writeInt8, unsafeWriteInt8 :: Int -> Int8 -> MutableDataView -> IO ()
writeInt8       idx x dv = IO (I.js_setInt8       idx x dv)
unsafeWriteInt8 idx x dv = IO (I.js_unsafeSetInt8 idx x dv)
{-# INLINE writeInt8 #-}

writeUint8, unsafeWriteUint8 :: Int -> Word8 -> MutableDataView -> IO ()
writeUint8       idx x dv = IO (I.js_setUint8       idx x dv)
unsafeWriteUint8 idx x dv = IO (I.js_unsafeSetUint8 idx x dv)
{-# INLINE writeUint8 #-}

writeInt16LE, writeInt16BE, unsafeWriteInt16LE, unsafeWriteInt16BE
  :: Int -> Int16 -> MutableDataView -> IO ()
writeInt16LE       idx x dv = IO (I.js_setInt16LE       idx x dv)
writeInt16BE       idx x dv = IO (I.js_setInt16BE       idx x dv)
unsafeWriteInt16LE idx x dv = IO (I.js_unsafeSetInt16LE idx x dv)
unsafeWriteInt16BE idx x dv = IO (I.js_unsafeSetInt16BE idx x dv)
{-# INLINE writeInt16LE #-}
{-# INLINE writeInt16BE #-}
{-# INLINE unsafeWriteInt16LE #-}
{-# INLINE unsafeWriteInt16BE #-}

writeUint16LE, writeUint16BE, unsafeWriteUint16LE, unsafeWriteUint16BE
  :: Int -> Word16 -> MutableDataView -> IO ()
writeUint16LE       idx x dv = IO (I.js_setUint16LE       idx x dv)
writeUint16BE       idx x dv = IO (I.js_setUint16BE       idx x dv)
unsafeWriteUint16LE idx x dv = IO (I.js_unsafeSetUint16LE idx x dv)
unsafeWriteUint16BE idx x dv = IO (I.js_unsafeSetUint16BE idx x dv)
{-# INLINE writeUint16LE #-}
{-# INLINE writeUint16BE #-}
{-# INLINE unsafeWriteUint16LE #-}
{-# INLINE unsafeWriteUint16BE #-}

writeInt32LE, writeInt32BE, unsafeWriteInt32LE, unsafeWriteInt32BE
  :: Int -> Int -> MutableDataView -> IO ()
writeInt32LE       idx x dv = IO (I.js_setInt32LE       idx x dv)
writeInt32BE       idx x dv = IO (I.js_setInt32BE       idx x dv)
unsafeWriteInt32LE idx x dv = IO (I.js_unsafeSetInt32LE idx x dv)
unsafeWriteInt32BE idx x dv = IO (I.js_unsafeSetInt32BE idx x dv)
{-# INLINE writeInt32LE #-}
{-# INLINE writeInt32BE #-}
{-# INLINE unsafeWriteInt32LE #-}
{-# INLINE unsafeWriteInt32BE #-}

writeUint32LE, writeUint32BE, unsafeWriteUint32LE, unsafeWriteUint32BE
  :: Int -> Word -> MutableDataView -> IO ()
writeUint32LE       idx x dv = IO (I.js_setUint32LE       idx x dv)
writeUint32BE       idx x dv = IO (I.js_setUint32BE       idx x dv)
unsafeWriteUint32LE idx x dv = IO (I.js_unsafeSetUint32LE idx x dv)
unsafeWriteUint32BE idx x dv = IO (I.js_unsafeSetUint32BE idx x dv)
{-# INLINE writeUint32LE #-}
{-# INLINE writeUint32BE #-}
{-# INLINE unsafeWriteUint32LE #-}
{-# INLINE unsafeWriteUint32BE #-}

writeFloat32LE, writeFloat32BE, unsafeWriteFloat32LE, unsafeWriteFloat32BE
  :: Int -> Double -> MutableDataView -> IO ()
writeFloat32LE       idx x dv = IO (I.js_setFloat32LE       idx x dv)
writeFloat32BE       idx x dv = IO (I.js_setFloat32BE       idx x dv)
unsafeWriteFloat32LE idx x dv = IO (I.js_unsafeSetFloat32LE idx x dv)
unsafeWriteFloat32BE idx x dv = IO (I.js_unsafeSetFloat32BE idx x dv)
{-# INLINE writeFloat32LE #-}
{-# INLINE writeFloat32BE #-}
{-# INLINE unsafeWriteFloat32LE #-}
{-# INLINE unsafeWriteFloat32BE #-}

writeFloat64LE, writeFloat64BE, unsafeWriteFloat64LE, unsafeWriteFloat64BE
  :: Int -> Double -> MutableDataView -> IO ()
writeFloat64LE       idx x dv = IO (I.js_setFloat64LE       idx x dv)
writeFloat64BE       idx x dv = IO (I.js_setFloat64BE       idx x dv)
unsafeWriteFloat64LE idx x dv = IO (I.js_unsafeSetFloat64LE idx x dv)
unsafeWriteFloat64BE idx x dv = IO (I.js_unsafeSetFloat64BE idx x dv)
{-# INLINE writeFloat64LE #-}
{-# INLINE writeFloat64BE #-}
{-# INLINE unsafeWriteFloat64LE #-}
{-# INLINE unsafeWriteFloat64BE #-}

