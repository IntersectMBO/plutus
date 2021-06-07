{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI, UnliftedFFITypes,
             MagicHash, PolyKinds, BangPatterns
  #-}
{-|
    GHCJS implements the ByteArray# primitive with a JavaScript object
    containing an ArrayBuffer and various TypedArray views. This module
    contains utilities for manipulating and converting the buffer as
    a JavaScript object.

    None of the properties of a Buffer object should be written to in foreign
    code. Changing the contents of a MutableBuffer in foreign code is allowed.
 -}

-- fixme alignment not done yet!
module GHCJS.Buffer
    ( Buffer
    , MutableBuffer
    , create
    , createFromArrayBuffer
    , thaw, freeze, clone
      -- * JavaScript properties
    , byteLength
    , getArrayBuffer
    , getUint8Array
    , getUint16Array
    , getInt32Array
    , getDataView
    , getFloat32Array
    , getFloat64Array
      -- * primitive
    , toByteArray, fromByteArray
    , toByteArrayPrim, fromByteArrayPrim
    , toMutableByteArray, fromMutableByteArray
    , toMutableByteArrayPrim, fromMutableByteArrayPrim
      -- * bytestring
    , toByteString, fromByteString
      -- * pointers
    , toPtr, unsafeToPtr
    ) where

import GHC.Exts (ByteArray#, MutableByteArray#, Addr#, Ptr(..), Any)

import GHCJS.Buffer.Types
import GHCJS.Prim
import GHCJS.Internal.Types

import Data.Int
import Data.Word
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BS
import qualified Data.ByteString.Internal as BS
import Data.Primitive.ByteArray

import qualified JavaScript.TypedArray.Internal.Types as I
import           JavaScript.TypedArray.ArrayBuffer.Internal (SomeArrayBuffer)
import           JavaScript.TypedArray.DataView.Internal    (SomeDataView)
import qualified JavaScript.TypedArray.Internal as I

import GHC.ForeignPtr

create :: Int -> IO MutableBuffer
create n | n >= 0    = js_create n
         | otherwise = error "create: negative size"
{-# INLINE create #-}

createFromArrayBuffer :: SomeArrayBuffer any -> SomeBuffer any
createFromArrayBuffer buf = js_wrapBuffer buf
{-# INLINE createFromArrayBuffer #-}

getArrayBuffer :: SomeBuffer any -> SomeArrayBuffer any
getArrayBuffer buf = js_getArrayBuffer buf
{-# INLINE getArrayBuffer #-}

getInt32Array :: SomeBuffer any -> I.SomeInt32Array any
getInt32Array buf = js_getInt32Array buf
{-# INLINE getInt32Array #-}

getUint8Array :: SomeBuffer any -> I.SomeUint8Array any
getUint8Array buf = js_getUint8Array buf
{-# INLINE getUint8Array #-}

getUint16Array :: SomeBuffer any -> I.SomeUint16Array any
getUint16Array buf = js_getUint16Array buf
{-# INLINE getUint16Array #-}

getFloat32Array :: SomeBuffer any -> I.SomeFloat32Array any
getFloat32Array buf = js_getFloat32Array buf
{-# INLINE getFloat32Array #-}

getFloat64Array :: SomeBuffer any -> I.SomeFloat64Array any
getFloat64Array buf = js_getFloat64Array buf
{-# INLINE getFloat64Array #-}

getDataView :: SomeBuffer any -> SomeDataView any
getDataView buf = js_getDataView buf
{-# INLINE getDataView #-}

freeze :: MutableBuffer -> IO Buffer
freeze x = js_clone x
{-# INLINE freeze #-}

thaw :: Buffer -> IO MutableBuffer
thaw buf  = js_clone buf
{-# INLINE thaw #-}

clone :: MutableBuffer -> IO (SomeBuffer any2)
clone buf = js_clone buf
{-# INLINE clone #-}

fromByteArray :: ByteArray -> Buffer
fromByteArray (ByteArray ba) = fromByteArrayPrim ba
{-# INLINE fromByteArray #-}

toByteArray :: Buffer -> ByteArray
toByteArray buf = ByteArray (toByteArrayPrim buf)
{-# INLINE toByteArray #-}

fromMutableByteArray :: MutableByteArray s -> Buffer
fromMutableByteArray (MutableByteArray mba) = fromMutableByteArrayPrim mba
{-# INLINE fromMutableByteArray #-}

fromByteArrayPrim :: ByteArray# -> Buffer
fromByteArrayPrim ba = SomeBuffer (js_fromByteArray ba)
{-# INLINE fromByteArrayPrim #-}

toByteArrayPrim :: Buffer -> ByteArray#
toByteArrayPrim buf = js_toByteArray buf
{-# INLINE toByteArrayPrim #-}

fromMutableByteArrayPrim :: MutableByteArray# s -> Buffer
fromMutableByteArrayPrim mba = SomeBuffer (js_fromMutableByteArray mba)
{-# INLINE fromMutableByteArrayPrim #-}

toMutableByteArray :: Buffer -> MutableByteArray s
toMutableByteArray buf = MutableByteArray (toMutableByteArrayPrim buf)
{-# INLINE toMutableByteArray #-}

toMutableByteArrayPrim :: Buffer -> MutableByteArray# s
toMutableByteArrayPrim (SomeBuffer buf) = js_toMutableByteArray buf
{-# INLINE toMutableByteArrayPrim #-}

-- | Convert a 'ByteString' into a triple of (buffer, offset, length)
-- Warning: if the 'ByteString''s internal 'ForeignPtr' has a
-- finalizer associated with it, the returned 'Buffer' will not count
-- as a reference for the purpose of determining when that finalizer
-- should run.
fromByteString :: ByteString -> (Buffer, Int, Int)
fromByteString (BS.PS fp off len) =
  -- not super happy with this.  What if the bytestring's foreign ptr
  -- has a nontrivial finalizer attached to it?  I don't think there's
  -- a way to do that without someone else messing with the PS constructor
  -- directly though.
  let !(Ptr addr) = unsafeForeignPtrToPtr fp
  in (js_fromAddr addr, off, len)
{-# INLINE fromByteString #-}

-- | Wrap a 'Buffer' into a 'ByteString' using the given offset
-- and length.
toByteString :: Int -> Maybe Int -> Buffer -> ByteString
toByteString off _ buf
  | off < 0                    = error "toByteString: negative offset"
  | off > byteLength buf       = error "toByteString: offset past end of buffer"
toByteString off (Just len) buf
  | len < 0                    = error "toByteString: negative length"
  | len > byteLength buf - off = error "toByteString: length past end of buffer"
  | otherwise                  = unsafeToByteString off len buf
toByteString off Nothing buf   = unsafeToByteString off (byteLength buf - off) buf

unsafeToByteString :: Int -> Int -> Buffer -> ByteString
unsafeToByteString off len buf@(SomeBuffer bufRef) =
  let fp = ForeignPtr (js_toAddr buf) (PlainPtr (js_toMutableByteArray bufRef))
  in BS.PS fp off len

toPtr :: MutableBuffer -> Ptr a
toPtr buf = Ptr (js_toAddr buf)
{-# INLINE toPtr #-}

unsafeToPtr :: Buffer -> Ptr a
unsafeToPtr buf = Ptr (js_toAddr buf)
{-# INLINE unsafeToPtr #-}

byteLength :: SomeBuffer any -> Int
byteLength buf = js_byteLength buf
{-# INLINE byteLength #-}

-- ----------------------------------------------------------------------------

foreign import javascript unsafe
  "h$newByteArray" js_create :: Int -> IO MutableBuffer
foreign import javascript unsafe
  "h$wrapBuffer" js_wrapBuffer :: SomeArrayBuffer any -> SomeBuffer any
foreign import javascript unsafe
  "h$wrapBuffer($1.buf.slice($1.u8.byteOffset, $1.len))"
  js_clone :: SomeBuffer any1 -> IO (SomeBuffer any2)
foreign import javascript unsafe
  "$1.len" js_byteLength :: SomeBuffer any -> Int
foreign import javascript unsafe
  "$1.buf" js_getArrayBuffer    :: SomeBuffer any -> SomeArrayBuffer any
foreign import javascript unsafe
  "$1.i3" js_getInt32Array      :: SomeBuffer any -> I.SomeInt32Array any
foreign import javascript unsafe
  "$1.u8" js_getUint8Array      :: SomeBuffer any -> I.SomeUint8Array  any
foreign import javascript unsafe
  "$1.u1" js_getUint16Array     :: SomeBuffer any -> I.SomeUint16Array any
foreign import javascript unsafe
  "$1.f3" js_getFloat32Array    :: SomeBuffer any -> I.SomeFloat32Array  any
foreign import javascript unsafe
  "$1.f6" js_getFloat64Array    :: SomeBuffer any -> I.SomeFloat64Array any
foreign import javascript unsafe
  "$1.dv" js_getDataView        :: SomeBuffer any -> SomeDataView any

-- ----------------------------------------------------------------------------
-- these things have the same representation (modulo boxing),
-- conversion is free

foreign import javascript unsafe  
  "$r = $1;" js_toByteArray          :: SomeBuffer any      -> ByteArray#
foreign import javascript unsafe  
  "$r = $1;" js_fromByteArray        :: ByteArray#          -> JSVal
foreign import javascript unsafe
  "$r = $1;" js_fromMutableByteArray :: MutableByteArray# s -> JSVal
foreign import javascript unsafe
  "$r = $1;" js_toMutableByteArray   :: JSVal               -> MutableByteArray# s
foreign import javascript unsafe
  "$r1 = $1; $r2 = 0;"  js_toAddr    :: SomeBuffer any      -> Addr#
foreign import javascript unsafe
  "$r = $1;" js_fromAddr             :: Addr#               -> SomeBuffer any
