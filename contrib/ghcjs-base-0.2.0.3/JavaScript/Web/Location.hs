{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE DeriveDataTypeable #-}

module JavaScript.Web.Location ( Location
                               , getWindowLocation
                               , getHref
                               , setHref
                               , getProtocol
                               , setProtocol
                               , getHost
                               , setHost
                               , getHostname
                               , setHostname
                               , getPort
                               , setPort
                               , getPathname
                               , setPathname
                               , getSearch
                               , setSearch
                               , getHash
                               , setHash
                               , getUsername
                               , setUsername
                               , getPassword
                               , setPassword
                               , getOrigin
                               , assign
                               , reload
                               , replace
                               ) where

import           Data.Typeable

import           Data.JSString (JSString)
import qualified Data.JSString as JSS

import           GHCJS.Types

newtype Location = Location JSVal deriving (Typeable)
instance IsJSVal Location

getWindowLocation :: IO Location
getWindowLocation = js_getWindowLocation
{-# INLINE getWindowLocation #-}

getHref :: Location -> IO JSString
getHref = js_getHref
{-# INLINE getHref #-}

setHref :: JSString -> Location -> IO ()
setHref = js_setHref
{-# INLINE setHref #-}

getProtocol :: Location -> IO JSString
getProtocol = js_getProtocol
{-# INLINE getProtocol #-}

setProtocol :: JSString -> Location -> IO ()
setProtocol = js_setProtocol
{-# INLINE setProtocol #-}

getHost :: Location -> IO JSString
getHost = js_getHost
{-# INLINE getHost #-}

setHost :: JSString -> Location -> IO ()
setHost = js_setHost
{-# INLINE setHost #-}

getHostname :: Location -> IO JSString
getHostname = js_getHostname
{-# INLINE getHostname #-}

setHostname :: JSString -> Location -> IO ()
setHostname = js_setHostname
{-# INLINE setHostname #-}

getPort :: Location -> IO JSString
getPort = js_getPort
{-# INLINE getPort #-}

setPort :: JSString -> Location -> IO ()
setPort = js_setPort
{-# INLINE setPort #-}

getPathname :: Location -> IO JSString
getPathname = js_getPathname
{-# INLINE getPathname #-}

setPathname :: JSString -> Location -> IO ()
setPathname = js_setPathname
{-# INLINE setPathname #-}

getSearch :: Location -> IO JSString
getSearch = js_getSearch
{-# INLINE getSearch #-}

setSearch :: JSString -> Location -> IO ()
setSearch = js_setSearch
{-# INLINE setSearch #-}

getHash :: Location -> IO JSString
getHash = js_getHash
{-# INLINE getHash #-}

setHash :: JSString -> Location -> IO ()
setHash = js_setHash
{-# INLINE setHash #-}

getUsername :: Location -> IO JSString
getUsername = js_getUsername
{-# INLINE getUsername #-}

setUsername :: JSString -> Location -> IO ()
setUsername = js_setUsername
{-# INLINE setUsername #-}

getPassword :: Location -> IO JSString
getPassword = js_getPassword
{-# INLINE getPassword #-}

setPassword :: JSString -> Location -> IO ()
setPassword = js_setPassword
{-# INLINE setPassword #-}

getOrigin :: Location -> IO JSString
getOrigin = js_getUsername
{-# INLINE getOrigin #-}

assign :: JSString -> Location -> IO ()
assign = js_assign
{-# INLINE assign #-}

reload :: Bool -> Location -> IO ()
reload = js_reload
{-# INLINE reload #-}

replace :: JSString -> Location -> IO ()
replace = js_assign
{-# INLINE replace #-}

-------------------------------------------------------------------------------

foreign import javascript safe "window.location" js_getWindowLocation :: IO Location

foreign import javascript unsafe "$1.href"     js_getHref     :: Location -> IO JSString
foreign import javascript unsafe "$1.protocol" js_getProtocol :: Location -> IO JSString
foreign import javascript unsafe "$1.host"     js_getHost     :: Location -> IO JSString
foreign import javascript unsafe "$1.hostname" js_getHostname :: Location -> IO JSString
foreign import javascript unsafe "$1.port"     js_getPort     :: Location -> IO JSString
foreign import javascript unsafe "$1.pathname" js_getPathname :: Location -> IO JSString
foreign import javascript unsafe "$1.search"   js_getSearch   :: Location -> IO JSString
foreign import javascript unsafe "$1.hash"     js_getHash     :: Location -> IO JSString
foreign import javascript unsafe "$1.username" js_getUsername :: Location -> IO JSString
foreign import javascript unsafe "$1.password" js_getPassword :: Location -> IO JSString
foreign import javascript unsafe "$1.origin"   js_getOrigin   :: Location -> IO JSString

foreign import javascript safe "$2.href = $1;"     js_setHref     :: JSString -> Location -> IO ()
foreign import javascript safe "$2.protocol = $1;" js_setProtocol :: JSString -> Location -> IO ()
foreign import javascript safe "$2.host = $1;"     js_setHost     :: JSString -> Location -> IO ()
foreign import javascript safe "$2.hostname = $1;" js_setHostname :: JSString -> Location -> IO ()
foreign import javascript safe "$2.port = $1;"     js_setPort     :: JSString -> Location -> IO ()
foreign import javascript safe "$2.pathname = $1;" js_setPathname :: JSString -> Location -> IO ()
foreign import javascript safe "$2.search = $1;"   js_setSearch   :: JSString -> Location -> IO ()
foreign import javascript safe "$2.hash = $1;"     js_setHash     :: JSString -> Location -> IO ()
foreign import javascript safe "$2.username = $1;" js_setUsername :: JSString -> Location -> IO ()
foreign import javascript safe "$2.password = $1;" js_setPassword :: JSString -> Location -> IO ()

foreign import javascript safe "$2.assign($1);"    js_assign      :: JSString -> Location -> IO ()
foreign import javascript safe "$2.reload($1);"    js_reload      :: Bool     -> Location -> IO ()
foreign import javascript safe "$2.replace($1);"   js_replace     :: JSString -> Location -> IO ()
