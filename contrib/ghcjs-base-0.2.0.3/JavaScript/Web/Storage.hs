{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI #-}

module JavaScript.Web.Storage ( localStorage
                              , sessionStorage
                              , Storage
                              , getLength
                              , getIndex
                              , getItem
                              , setItem
                              , removeItem
                              , clear
                              ) where

import GHCJS.Types

import Data.JSString
import Data.JSString.Internal.Type

import JavaScript.Web.Storage.Internal

localStorage :: Storage
localStorage = js_localStorage
{-# INLINE localStorage #-}

sessionStorage :: Storage
sessionStorage = js_sessionStorage
{-# INLINE sessionStorage #-}

getLength :: Storage -> IO Int
getLength s = js_getLength s
{-# INLINE getLength #-}

getIndex :: Int -> Storage -> IO (Maybe JSString)
getIndex i s = do
  r <- js_getIndex i s
  return $ if isNull r then Nothing else Just (JSString r)
{-# INLINE getIndex #-}

getItem :: JSString -> Storage -> IO (Maybe JSString)
getItem key s = do
  r <- js_getItem key s
  return $ if isNull r then Nothing else Just (JSString r)
{-# INLINE getItem #-}

setItem :: JSString -> JSString -> Storage -> IO ()
setItem key val s = js_setItem key val s
{-# INLINE setItem #-}

removeItem :: JSString -> Storage -> IO ()
removeItem key s = js_removeItem key s
{-# INLINE removeItem #-}

clear :: Storage -> IO ()
clear s = js_clear s
{-# INLINE clear #-}

-- -----------------------------------------------------------------------------

foreign import javascript unsafe
  "window.localStorage"   js_localStorage   :: Storage
foreign import javascript unsafe
  "window.sessionStorage" js_sessionStorage :: Storage
foreign import javascript unsafe
  "$1.length"             js_getLength      :: Storage -> IO Int
foreign import javascript unsafe
  "$2.key($1)"            js_getIndex       :: Int -> Storage -> IO JSVal
foreign import javascript unsafe
  "$2.getItem($1)"        js_getItem        :: JSString -> Storage -> IO JSVal
foreign import javascript safe
  "$3.setItem($1,$2)"     js_setItem        :: JSString -> JSString -> Storage -> IO ()
foreign import javascript unsafe
  "$2.removeItem($1)"     js_removeItem     :: JSString -> Storage -> IO ()
foreign import javascript unsafe
  "$1.clear();"           js_clear          :: Storage -> IO ()
