{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI, DeriveDataTypeable,
             UnboxedTuples, GHCForeignImportPrim, UnliftedFFITypes,
             MagicHash
  #-}

module JavaScript.Web.MessageEvent ( MessageEvent
                                   , getData
                                   , MessageEventData(..)
                                   ) where

import GHCJS.Types

import GHC.Exts

import Data.Typeable

import JavaScript.Web.MessageEvent.Internal

import JavaScript.Web.Blob.Internal (Blob, SomeBlob(..))
import JavaScript.TypedArray.ArrayBuffer.Internal (ArrayBuffer, SomeArrayBuffer(..))
import Data.JSString.Internal.Type (JSString(..))


data MessageEventData = StringData      JSString
                      | BlobData        Blob
                      | ArrayBufferData ArrayBuffer
  deriving (Typeable)

getData :: MessageEvent -> MessageEventData
getData me = case js_getData me of
               (# 1#, r #) -> StringData      (JSString r)
               (# 2#, r #) -> BlobData        (SomeBlob r)
               (# 3#, r #) -> ArrayBufferData (SomeArrayBuffer r)
{-# INLINE getData #-}



-- -----------------------------------------------------------------------------

foreign import javascript unsafe
  "$r2 = $1.data;\
  \$r1 = typeof $r2 === 'string' ? 1 : ($r2 instanceof ArrayBuffer ? 3 : 2)"
  js_getData :: MessageEvent -> (# Int#, JSVal #)
