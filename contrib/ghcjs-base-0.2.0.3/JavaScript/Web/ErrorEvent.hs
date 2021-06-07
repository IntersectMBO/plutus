{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE JavaScriptFFI #-}

module JavaScript.Web.ErrorEvent ( ErrorEvent
                                 , message
                                 , filename
                                 , lineno
                                 , colno
                                 , error
                                 ) where

import Prelude hiding (error)

import GHCJS.Types

import Data.JSString

import JavaScript.Web.ErrorEvent.Internal

message :: ErrorEvent -> JSString
message ee = js_getMessage ee
{-# INLINE message #-}

filename :: ErrorEvent -> JSString
filename ee = js_getFilename ee
{-# INLINE filename #-}

lineno :: ErrorEvent -> Int
lineno ee = js_getLineno ee
{-# INLINE lineno #-}

colno :: ErrorEvent -> Int
colno ee = js_getColno ee
{-# INLINE colno #-}

error :: ErrorEvent -> JSVal
error ee = js_getError ee
{-# INLINE error #-}

-- -----------------------------------------------------------------------------

foreign import javascript unsafe "$1.message"
  js_getMessage  :: ErrorEvent -> JSString
foreign import javascript unsafe "$1.filename"
  js_getFilename :: ErrorEvent -> JSString
foreign import javascript unsafe "$1.lineno"
  js_getLineno   :: ErrorEvent -> Int
foreign import javascript unsafe "$1.colno"
  js_getColno    :: ErrorEvent -> Int
foreign import javascript unsafe "$1.error"
  js_getError    :: ErrorEvent -> JSVal
