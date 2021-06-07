{-# LANGUAGE MagicHash, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module JavaScript.TypedArray.ST
    ( {- STTypedArray(..)
    , -} STInt8Array, STInt16Array, STInt32Array
    , STUint8Array, STUint16Array, STUint32Array
    , STFloat32Array, STFloat64Array
    , STUint8ClampedArray
    , length
    , byteLength
    , byteOffset
    , buffer
    , subarray
    ) where


import Prelude ( Maybe, undefined )

import GHC.Exts
import GHC.ST
import GHC.Int
import GHC.Word

import GHCJS.Types

import GHCJS.Buffer.Types
import GHCJS.Prim
import GHCJS.Internal.Types

import qualified Data.ByteString as B
import           Data.Primitive.ByteArray

import qualified JavaScript.Array.Internal as JSA

import qualified JavaScript.TypedArray.Internal as I
import           JavaScript.TypedArray.Internal ( length, byteLength, byteOffset, buffer, subarray ) 
import           JavaScript.TypedArray.Internal.Types
import           JavaScript.TypedArray.ArrayBuffer.Internal
  ( SomeArrayBuffer, MutableArrayBuffer, STArrayBuffer )
import           JavaScript.TypedArray.DataView.Internal ( SomeDataView )

class STTypedArray s a where
  unsafeIndex     :: Int           -> a -> ST s (Elem a)
  index           :: Int           -> a -> ST s (Elem a)
  unsafeSetIndex  :: Int -> Elem a -> a -> ST s ()
  setIndex        :: Int -> Elem a -> a -> ST s ()
  create          :: Int                -> ST s a
--  fromArray       :: JSArray e          -> ST s a
  fromBuffer      :: STArrayBuffer s    -> Int    -> Maybe Int -> ST s a
  indexOf         :: Int                -> Elem a -> a -> ST s Int
  lastIndexOf     :: Int                -> Elem a -> a -> ST s Int

instance STTypedArray s (STInt8Array s) where
  index i a                  = ST (I.indexI8 i a)
  unsafeIndex i a            = ST (I.unsafeIndexI8 i a)
  setIndex i (I8# x) a       = ST (I.setIndexI i x a)
  unsafeSetIndex i (I8# x) a = ST (I.unsafeSetIndexI i x a)
  indexOf s (I8# x) a        = ST (I.indexOfI s x a)
  fromBuffer                 = undefined
  lastIndexOf s (I8# x) a    = ST (I.lastIndexOfI s x a)
  create l                   = ST (I.js_createInt8Array l)

-- ---------------------------------------------------------------------------
{-
setIndexI :: SomeTypedArray e m -> Int -> Int# -> ST s ()
setIndexI a i x = ST (I.js_setIndexI a i x)
{-# INLINE setIndexI #-}

unsafeSetIndexI :: SomeTypedArray e m -> Int -> Int# -> ST s ()
unsafeSetIndexI a i x = ST (I.js_unsafeSetIndexI a i x)
{-# INLINE unsafeSetIndexI #-}

setIndexW :: SomeTypedArray e m -> Int -> Word# -> ST s ()
setIndexW a i x = ST (I.js_setIndexW a i x)
{-# INLINE setIndexW #-}

unsafeSetIndexW :: SomeTypedArray e m -> Int -> Word# -> ST s ()
unsafeSetIndexW a i x = ST (I.js_unsafeSetIndexW a i x)
{-# INLINE unsafeSetIndexW #-}

indexOfI :: SomeTypedArray e m -> Int# -> ST s Int
indexOfI a x = ST (I.js_indexOfI a x)
{-# INLINE indexOfI #-}

indexOfW :: SomeTypedArray e m -> Word# -> ST s Int
indexOfW a x = ST (I.js_indexOfW a x)
{-# INLINE indexOfW #-}
-}
-- ---------------------------------------------------------------------------
{-
length :: SomeSTTypedArray s e -> Int
length x = I.length x -- ST (I.js_length x)
{-# INLINE length #-}

byteLength :: SomeSTTypedArray s e -> Int
byteLength x = ST (I.js_byteLength x)
{-# INLINE byteLength #-}

byteOffset :: SomeSTTypedArray s e -> Int
byteOffset x = ST (I.js_byteOffset x)
{-# INLINE byteOffset #-}

buffer :: SomeSTTypedArray s e -> STArrayBuffer s
buffer x = ST (I.js_buffer x)
{-# INLINE buffer #-}

subarray :: Int -> Int -> SomeSTTypedArray s e -> SomeSTTypedArray s e
subarray begin end x = ST (I.js_subarray begin end x)
{-# INLINE subarray #-}

-- fixme convert JSException to Haskell exception
set :: SomeSTTypedArray s e -> Int -> SomeSTTypedArray s e  -> ST s ()
set src offset dest = ST (I.js_set src offset dest)
{-# INLINE set #-}

unsafeSet :: SomeSTTypedArray s e -> Int -> SomeSTTypedArray s e -> ST s ()
unsafeSet src offset dest = ST (I.js_unsafeSet src offset dest)
{-# INLINE unsafeSet #-}

-}
