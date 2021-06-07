{-# LANGUAGE RankNTypes, OverloadedStrings, DeriveDataTypeable,
             ForeignFunctionInterface, JavaScriptFFI, EmptyDataDecls,
             TypeFamilies, DataKinds, ScopedTypeVariables,
             FlexibleContexts, FlexibleInstances, TypeSynonymInstances,
             LambdaCase, MultiParamTypeClasses, DeriveGeneric #-}

module JavaScript.Web.XMLHttpRequest ( xhr
                                     , xhrByteString
                                     , xhrText
                                     , xhrString
                                     , Method(..)
                                     , Request(..)
                                     , RequestData(..)
                                     , Response(..)
                                     , ResponseType(..)
                                     , FormDataVal(..)
                                     , XHRError(..)
                                     ) where

import Control.Applicative
import Control.Exception
import Control.Monad

import GHCJS.Types
import GHCJS.Prim
import GHCJS.Marshal
import GHCJS.Marshal.Pure
import GHCJS.Internal.Types

import qualified GHCJS.Buffer as Buffer

import GHC.Generics

import Data.ByteString
import Data.Data
import Data.JSString
import Data.JSString.Internal.Type ( JSString(..) )
import Data.Typeable
import Data.Proxy
import Data.Text (Text)

import           Data.JSString.Text (textFromJSString)
import qualified Data.JSString as JSS

import JavaScript.JSON.Types.Internal ( SomeValue(..) )
import JavaScript.TypedArray.Internal.Types ( SomeTypedArray(..) )
import JavaScript.TypedArray.ArrayBuffer ( ArrayBuffer(..) )
import JavaScript.TypedArray.ArrayBuffer.Internal ( SomeArrayBuffer(..) )

import JavaScript.Web.Blob
import JavaScript.Web.Blob.Internal

import JavaScript.Web.File

data Method = GET | POST | PUT | DELETE | Method JSString
  deriving (Show, Eq, Ord)

data XHRError = XHRError String
              | XHRAborted
              deriving (Generic, Data, Typeable, Show, Eq) 

instance Exception XHRError

methodJSString :: Method -> JSString
methodJSString GET    = "GET"
methodJSString POST   = "POST"
methodJSString PUT    = "PUT"
methodJSString DELETE = "DELETE"
methodJSString (Method m) = m

type Header = (JSString, JSString)

data FormDataVal = StringVal JSString
                 | BlobVal   Blob     (Maybe JSString)
                 | FileVal   File     (Maybe JSString)
  deriving (Typeable)

data Request = Request { reqMethod          :: Method
                       , reqURI             :: JSString
                       , reqLogin           :: Maybe (JSString, JSString)
                       , reqHeaders         :: [Header]
                       , reqWithCredentials :: Bool
                       , reqData            :: RequestData
                       }
  deriving (Typeable)

data RequestData = NoData
                 | StringData     JSString
                 | TypedArrayData (forall e. SomeTypedArray e Immutable)
                 | FormData       [(JSString, FormDataVal)]
  deriving (Typeable)

data Response a = Response { contents              :: Maybe a
                           , status                :: Int
                           , getAllResponseHeaders :: IO JSString
                           , getResponseHeader     :: JSString -> IO (Maybe JSString)
                           }

instance Functor Response where fmap f r = r { contents = fmap f (contents r) }

class ResponseType a where
    getResponseTypeString :: Proxy a  -> JSString
    wrapResponseType      :: JSVal -> a

instance ResponseType ArrayBuffer where
  getResponseTypeString _ = "arraybuffer"
  wrapResponseType        = SomeArrayBuffer

instance m ~ Immutable => ResponseType JSString where
  getResponseTypeString _ = "text"
  wrapResponseType        = JSString

instance ResponseType Blob where
  getResponseTypeString _ = "blob"
  wrapResponseType        = SomeBlob

instance m ~ Immutable => ResponseType (SomeValue m) where
  getResponseTypeString _ = "json"
  wrapResponseType        = SomeValue

newtype JSFormData = JSFormData JSVal deriving (Typeable)

newtype XHR = XHR JSVal deriving (Typeable)

-- -----------------------------------------------------------------------------
-- main entry point

xhr :: forall a. ResponseType a => Request -> IO (Response a)
xhr req = js_createXHR >>= \x ->
  let doRequest = do
        case reqLogin req of
          Nothing           ->
            js_open2 (methodJSString (reqMethod req)) (reqURI req) x
          Just (user, pass) ->
            js_open4 (methodJSString (reqMethod req)) (reqURI req) user pass x
        js_setResponseType
          (getResponseTypeString (Proxy :: Proxy a)) x
        forM_ (reqHeaders req) (\(n,v) -> js_setRequestHeader n v x)
        
        case reqWithCredentials req of
          True  -> js_setWithCredentials x
          False -> return ()
        
        r <- case reqData req of
          NoData                            ->
            js_send0 x
          StringData str                    ->
            js_send1 (pToJSVal str) x
          TypedArrayData (SomeTypedArray t) ->
            js_send1 t x
          FormData xs                       -> do
            fd@(JSFormData fd') <- js_createFormData
            forM_ xs $ \(name, val) -> case val of
              StringVal str               ->
                js_appendFormData2 name (pToJSVal str) fd
              BlobVal (SomeBlob b) mbFile ->
                appendFormData name b mbFile fd
              FileVal (SomeBlob b) mbFile ->
                appendFormData name b mbFile fd
            js_send1 fd' x
        case r of
          0 -> do
            status <- js_getStatus x
            r      <- do
              hr <- js_hasResponse x
              if hr then Just . wrapResponseType <$> js_getResponse x
                    else pure Nothing
            return $ Response r
                              status
                              (js_getAllResponseHeaders x)
                              (\h -> getResponseHeader' h x)
          1 -> throwIO XHRAborted
          2 -> throwIO (XHRError "network request error")
  in doRequest `onException` js_abort x

appendFormData :: JSString -> JSVal
               -> Maybe JSString -> JSFormData -> IO ()
appendFormData name val Nothing         fd =
  js_appendFormData2 name val fd
appendFormData name val (Just fileName) fd =
  js_appendFormData3 name val fileName fd

getResponseHeader' :: JSString -> XHR -> IO (Maybe JSString)
getResponseHeader' name x = do
  h <- js_getResponseHeader name x
  return $ if isNull h then Nothing else Just (JSString h)

-- -----------------------------------------------------------------------------
-- utilities

xhrString :: Request -> IO (Response String)
xhrString = fmap (fmap JSS.unpack) . xhr

xhrText :: Request -> IO (Response Text)
xhrText = fmap (fmap textFromJSString) . xhr

xhrByteString :: Request -> IO (Response ByteString)
xhrByteString = fmap
  (fmap (Buffer.toByteString 0 Nothing . Buffer.createFromArrayBuffer)) . xhr

-- -----------------------------------------------------------------------------

foreign import javascript unsafe
  "$1.withCredentials = true;"
  js_setWithCredentials :: XHR -> IO ()

foreign import javascript unsafe
  "new XMLHttpRequest()"
  js_createXHR :: IO XHR
foreign import javascript unsafe
  "$2.responseType = $1;"
  js_setResponseType :: JSString -> XHR -> IO ()
foreign import javascript unsafe
  "$1.abort();"
  js_abort :: XHR -> IO ()
foreign import javascript unsafe
  "$3.setRequestHeader($1,$2);"
  js_setRequestHeader :: JSString -> JSString -> XHR -> IO ()
foreign import javascript unsafe
  "$3.open($1,$2)"
  js_open2 :: JSString -> JSString -> XHR -> IO ()
foreign import javascript unsafe
  "$5.open($1,$2,true,$4,$5);"
  js_open4 :: JSString -> JSString -> JSString -> JSString -> XHR -> IO ()
foreign import javascript unsafe
  "new FormData()"
  js_createFormData :: IO JSFormData
foreign import javascript unsafe
  "$3.append($1,$2)"
  js_appendFormData2 :: JSString -> JSVal -> JSFormData -> IO ()
foreign import javascript unsafe
  "$4.append($1,$2,$3)"
  js_appendFormData3 :: JSString -> JSVal -> JSString -> JSFormData -> IO ()
foreign import javascript unsafe
  "$1.status"
  js_getStatus :: XHR -> IO Int
foreign import javascript unsafe
  "$1.response"
  js_getResponse :: XHR -> IO JSVal
foreign import javascript unsafe
  "$1.response ? true : false"
  js_hasResponse :: XHR -> IO Bool
foreign import javascript unsafe
  "$1.getAllResponseHeaders()"
  js_getAllResponseHeaders :: XHR -> IO JSString
foreign import javascript unsafe
  "$2.getResponseHeader($1)"
  js_getResponseHeader :: JSString -> XHR -> IO JSVal

-- -----------------------------------------------------------------------------

foreign import javascript interruptible
  "h$sendXHR($1, null, $c);"
  js_send0 :: XHR -> IO Int
foreign import javascript interruptible
  "h$sendXHR($2, $1, $c);"
  js_send1 :: JSVal -> XHR -> IO Int
