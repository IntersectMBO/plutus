{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI #-}

module JavaScript.Web.StorageEvent ( StorageEvent
                                   , key
                                   , oldValue
                                   , newValue
                                   , url
                                   , storageArea
                                   ) where

import Data.JSString
--import Data.JSString.Internal -- fixme
import Data.JSString.Internal.Type -- fixme

import GHCJS.Types

import JavaScript.Web.Storage.Internal

key :: StorageEvent -> Maybe JSString
key se | isNull r  = Nothing
       | otherwise = Just (JSString r)
  where
    r = js_getKey se
{-# INLINE key #-}

oldValue :: StorageEvent -> Maybe JSString
oldValue se | isNull r  = Nothing
            | otherwise = Just (JSString r)
  where
    r = js_getOldValue se
{-# INLINE oldValue #-}

newValue :: StorageEvent -> Maybe JSString
newValue se | isNull r  = Nothing
            | otherwise = Just (JSString r)
  where
    r = js_getNewValue se
{-# INLINE newValue #-}

url :: StorageEvent -> JSString
url se = js_getUrl se
{-# INLINE url #-}

storageArea :: StorageEvent -> Maybe Storage
storageArea se | isNull r  = Nothing
               | otherwise = Just (Storage r)
  where
    r = js_getStorageArea se
{-# INLINE storageArea #-}

-- -----------------------------------------------------------------------------

foreign import javascript unsafe
  "$1.key"         js_getKey         :: StorageEvent -> JSVal
foreign import javascript unsafe
  "$1.oldValue"    js_getOldValue    :: StorageEvent -> JSVal
foreign import javascript unsafe
  "$1.newValue"    js_getNewValue    :: StorageEvent -> JSVal
foreign import javascript unsafe
  "$1.url"         js_getUrl         :: StorageEvent -> JSString
foreign import javascript unsafe
  "$1.storageArea" js_getStorageArea :: StorageEvent -> JSVal
