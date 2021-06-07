{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE InterruptibleFFI #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE UnboxedTuples #-}

module JavaScript.Web.WebSocket ( WebSocket
                                , WebSocketRequest(..)
                                , ReadyState(..)
                                , BinaryType(..)
                                , connect
                                , close
                                , send
                                , sendArrayBuffer
                                , sendBlob
                                , getBufferedAmount
                                , getExtensions
                                , getProtocol
                                , getReadyState
                                , getBinaryType
                                , setBinaryType
                                , getUrl
                                ) where

import           GHCJS.Concurrent
import           GHCJS.Prim
import           GHCJS.Foreign.Callback.Internal (Callback(..))
import qualified GHCJS.Foreign.Callback          as CB

import           GHC.Exts

import           Control.Exception
import           Control.Monad

import           Data.Data
import           Data.Maybe
import           Data.Typeable

import           System.IO

import           Data.JSString (JSString)
import qualified Data.JSString as JSS

import           JavaScript.Array (JSArray)
import qualified JavaScript.Array as JSA
import           JavaScript.TypedArray.ArrayBuffer (ArrayBuffer)
import           JavaScript.Web.Blob (Blob)
import           JavaScript.Web.MessageEvent
import           JavaScript.Web.MessageEvent.Internal
import           JavaScript.Web.CloseEvent
import           JavaScript.Web.CloseEvent.Internal
import           JavaScript.Web.ErrorEvent
import           JavaScript.Web.ErrorEvent.Internal

import Unsafe.Coerce

data WebSocketRequest = WebSocketRequest
  { url       :: JSString
  , protocols :: [JSString]
  , onClose   :: Maybe (CloseEvent -> IO ()) -- ^ called when the connection closes (at most once)
  , onMessage :: Maybe (MessageEvent -> IO ()) -- ^ called for each message
  }

newtype WebSocket = WebSocket JSVal
-- instance IsJSVal WebSocket

data ReadyState = Connecting | Open | Closing | Closed
  deriving (Data, Typeable, Enum, Eq, Ord, Show)

data BinaryType = Blob | ArrayBuffer
  deriving (Data, Typeable, Enum, Eq, Ord, Show)

{- | create a WebSocket -} 
connect :: WebSocketRequest -> IO WebSocket
connect req = do
  mcb <- maybeCallback MessageEvent (onMessage req)
  ccb <- maybeCallback CloseEvent   (onClose req)
  withoutPreemption $ do
    ws <- case protocols req of
           []  -> js_createDefault (url req)
           [x] -> js_createStr     (url req) x
    (js_open ws mcb ccb >>= handleOpenErr >> return ws) `onException` js_close 1000 "Haskell Exception" ws

maybeCallback :: (JSVal -> a) -> Maybe (a -> IO ()) -> IO JSVal
maybeCallback _ Nothing = return jsNull
maybeCallback f (Just g) = do
  Callback cb <- CB.syncCallback1 CB.ContinueAsync (g . f)
  return cb

handleOpenErr :: JSVal -> IO ()
handleOpenErr r
  | isNull r  = return ()
  | otherwise = throwIO (userError "WebSocket failed to connect") -- fixme

{- | close a websocket and release the callbacks -}
close :: Maybe Int -> Maybe JSString -> WebSocket -> IO ()
close value reason ws =
  js_close (fromMaybe 1000 value) (fromMaybe JSS.empty reason) ws
{-# INLINE close #-}

send :: JSString -> WebSocket -> IO ()
send xs ws = js_send xs ws
{-# INLINE send #-}

sendBlob :: Blob -> WebSocket -> IO ()
sendBlob = js_sendBlob
{-# INLINE sendBlob #-}

sendArrayBuffer :: ArrayBuffer -> WebSocket -> IO ()
sendArrayBuffer = js_sendArrayBuffer
{-# INLINE sendArrayBuffer #-}

getBufferedAmount :: WebSocket -> IO Int
getBufferedAmount ws = js_getBufferedAmount ws
{-# INLINE getBufferedAmount #-}

getExtensions :: WebSocket -> IO JSString
getExtensions ws = js_getExtensions ws
{-# INLINE getExtensions #-}

getProtocol :: WebSocket -> IO JSString
getProtocol ws = js_getProtocol ws
{-# INLINE getProtocol #-}

getReadyState :: WebSocket -> IO ReadyState
getReadyState ws = fmap toEnum (js_getReadyState ws)
{-# INLINE getReadyState #-}

getBinaryType :: WebSocket -> IO BinaryType
getBinaryType ws = fmap toEnum (js_getBinaryType ws)
{-# INLINE getBinaryType #-}

getUrl :: WebSocket -> JSString
getUrl ws = js_getUrl ws
{-# INLINE getUrl #-}

getLastError :: WebSocket -> IO (Maybe ErrorEvent)
getLastError ws = do
  le <- js_getLastError ws
  return $ if isNull le then Nothing else Just (ErrorEvent le)
{-# INLINE getLastError #-}

setBinaryType :: BinaryType -> WebSocket -> IO ()
setBinaryType Blob = js_setBinaryType (JSS.pack "blob")
setBinaryType ArrayBuffer = js_setBinaryType (JSS.pack "arraybuffer")

-- -----------------------------------------------------------------------------

foreign import javascript safe
   "new WebSocket($1)" js_createDefault :: JSString -> IO WebSocket
foreign import javascript safe
  "new WebSocket($1, $2)" js_createStr :: JSString -> JSString -> IO WebSocket
foreign import javascript safe
  "new WebSocket($1, $2)" js_createArr :: JSString -> JSArray -> IO WebSocket

foreign import javascript interruptible
  "h$openWebSocket($1, $2, $3, $c);"
  js_open  :: WebSocket -> JSVal -> JSVal -> IO JSVal
foreign import javascript safe
  "h$closeWebSocket($1, $2, $3);"
  js_close :: Int -> JSString -> WebSocket -> IO ()
foreign import javascript unsafe
  "$2.send($1);"          js_send              :: JSString -> WebSocket -> IO ()
foreign import javascript unsafe
  "$2.send($1);"          js_sendBlob          :: Blob -> WebSocket -> IO ()
foreign import javascript unsafe
  "$2.send($1);"          js_sendArrayBuffer   :: ArrayBuffer -> WebSocket -> IO ()
foreign import javascript unsafe
  "$1.bufferedAmount"     js_getBufferedAmount :: WebSocket -> IO Int
foreign import javascript unsafe
  "$1.readyState"         js_getReadyState     :: WebSocket -> IO Int
foreign import javascript unsafe
  "$1.protocol"           js_getProtocol       :: WebSocket -> IO JSString
foreign import javascript unsafe
  "$1.extensions"         js_getExtensions     :: WebSocket -> IO JSString
foreign import javascript unsafe
  "$1.url"                js_getUrl            :: WebSocket -> JSString
foreign import javascript unsafe
  "$1.binaryType === 'blob' ? 0 : 1"
  js_getBinaryType                             :: WebSocket -> IO Int
foreign import javascript unsafe
  "$1.lastError"          js_getLastError      :: WebSocket -> IO JSVal

foreign import javascript unsafe
  "$2.binaryType = $1"
  js_setBinaryType                             :: JSString -> WebSocket -> IO ()
