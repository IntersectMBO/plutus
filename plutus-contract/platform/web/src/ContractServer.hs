{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}


module ContractServer
    ( serveContract
    ) where

import qualified Servant.Server         as Servant

import           GHCJS.Types (jsval)
import           GHCJS.Prim             (fromJSString, JSVal, fromJSArray, toJSArray, getProp)
import           GHCJS.Foreign.Callback (asyncCallback1, Callback)

import           Data.ByteString          (ByteString)
import qualified Data.ByteString          as BS
import           Data.ByteString.Builder  (toLazyByteString)
import qualified Data.ByteString.Internal as BS

import qualified Data.ByteString.Char8  as BC8
import qualified Data.ByteString.Lazy   as BL

import qualified Data.CaseInsensitive   as CI

import           Data.Text              (Text)

import           Language.Plutus.Contract          (Contract)
import           Language.Plutus.Contract.Servant (contractApp, ContractAPI)
import           Servant.Server                        (Application, ServantErr, Server, serve)

import           Network.HTTP.Types.Header (Header, ResponseHeaders, hHost, hRange, hReferer, hUserAgent)
import           Network.HTTP.Types.Method (Method)
import           Network.HTTP.Types.Status (statusCode, Status, internalServerError500)
import           Network.HTTP.Types.URI (Query, parseQuery, decodePathSegments)
import           Network.HTTP.Types.Version (http11)

import           Network.Wai.Internal (Request(..), Response(..), ResponseReceived(..))
import           Network.Wai (Application, RequestBodyLength(..), FilePart, filePartOffset, filePartByteCount)

import qualified Data.Vault.Lazy as Vault

import           System.IO (Handle, SeekMode(..), hSeek, hClose, IOMode(..), openFile)

import           Control.Exception (SomeException, try, bracket)
import           Network.Socket (SockAddr(..))
import           Data.Coerce
import           Data.IORef             (atomicModifyIORef, newIORef)
import           Data.List              (uncons)
import           Data.Tuple             (swap)
import           Data.Proxy             (Proxy)
import           GHC.ForeignPtr
import           GHC.Prim

import System.IO


serveContract :: Application -> IO ()
serveContract app = serveCallback app

-- | Serve a 'PlutusContract' via the contract API.
serveCallback :: Application -> IO ()
serveCallback app = do
  callback <- asyncCallback1 (serveJSCallback app)
  js_setCallback (jsval callback)

{-
  This handles requests for the WAI Application
 -}
serveJSCallback :: Application -> JSVal -> IO ()
serveJSCallback app = \req -> do
  methodBs <- getRequestMethod req
  pathBs   <- getRequestURL    req
  options  <- getProp req "options"
  -- we only support a single chunk, non-streaming body for now
  bodyBs   <- getRequestBody options
  bodyRef  <- newIORef [bodyBs]
  headers  <- getRequestHeaders options
  callback <- getProp req "callback"
  let (pathSegments, rawQueryString, queryString) = decodePath' pathBs
      request = Request
            { requestMethod          = methodBs
            , httpVersion            = http11
            , rawPathInfo            = pathBs
            , requestHeaders         = headers
            , rawQueryString         = rawQueryString
            , isSecure               = False
            , remoteHost             = SockAddrUnix "/dev/null"
            , pathInfo               = pathSegments
            , queryString            = queryString
            , requestBody            =
                atomicModifyIORef bodyRef $ maybe ([], mempty) swap . uncons
            , vault                  = Vault.empty
            , requestBodyLength      =
                KnownLength (fromIntegral (BS.length bodyBs))
            , requestHeaderHost      = lookup hHost      headers
            , requestHeaderRange     = lookup hRange     headers
            , requestHeaderReferer   = lookup hReferer   headers
            , requestHeaderUserAgent = lookup hUserAgent headers
            }
      respond :: Response -> IO ResponseReceived
      respond (ResponseFile status headers filePath mbFilePart) = do
        result <- try (readFilePart filePath mbFilePart)
        case result of
          Left (e :: SomeException) -> respondError (show e)
          Right body                -> respondWith status headers body
      respond (ResponseStream status headers streamingBody) =
        respondError "ResponseStream response type not supported"
      respond (ResponseBuilder status headers builder) =
        respondWith status headers (BL.toStrict $ toLazyByteString builder)
      respond (ResponseRaw _ fallback) = respond fallback

      respondError :: String
                   -> IO ResponseReceived
      respondError msg = respondWith internalServerError500 [] (BC8.pack msg)

      respondWith :: Status
                  -> ResponseHeaders
                  -> ByteString
                  -> IO ResponseReceived
      respondWith status headers body = do
        hs <- mkResponseHeaders headers
        js_respond (statusCode status) hs (fromByteString body) callback
        pure ResponseReceived

  ResponseReceived <- app request respond
  pure ()

readFilePart :: FilePath -> Maybe FilePart -> IO ByteString
readFilePart fileName Nothing = BS.readFile fileName
readFilePart fileName (Just filePart) =
  bracket (openFile fileName ReadMode) hClose $ \h -> do
          hSeek h AbsoluteSeek (filePartOffset filePart)
          BS.concat <$> readBytes h (fromIntegral $ filePartByteCount filePart)

readBytes :: Handle -> Int -> IO [ByteString]
readBytes _ 0 = pure []
readBytes h n = do
  b <- BS.hGet h n
  if BS.null b then pure []
              else (b:) <$> readBytes h (n - BS.length b)

-- | Decode a whole path (path segments + query).
--   based on Network.HTTP.Types.URI.html.decodePath
decodePath' :: ByteString -> ([Text], ByteString, Query)
decodePath' b =
    let (x, y) = BS.break (== 63) b -- question mark
    in (decodePathSegments x, y, parseQuery y)

getRequestMethod :: JSVal -> IO Method
getRequestMethod req = toByteString <$> getProp req "method"

getRequestURL :: JSVal -> IO ByteString
getRequestURL req = toByteString <$> getProp req "url"

getRequestBody :: JSVal -> IO ByteString
getRequestBody options = toByteString <$> getProp options "body"

getRequestHeaders :: JSVal -> IO [Header]
getRequestHeaders options =
  concat <$> (mapM convertHeader =<< fromJSArray =<< getProp options "headers")
  where
    convertHeader :: JSVal -> IO [Header]
    convertHeader pair =
      (map toByteString <$> fromJSArray pair) >>=
        \case
          [name, value] | not (BS.null name) && not (BS.null value) ->
            pure [(CI.mk name, value)]
          _ -> pure []

mkResponseHeaders :: ResponseHeaders -> IO JSVal
mkResponseHeaders headers =
  mapM (\(name, val) -> toJSArray (map fromByteString [CI.original name, val])) headers >>=
  toJSArray

toByteString :: JSVal -> ByteString
toByteString val =
  BS.PS (ForeignPtr (js_toAddr val) (PlainPtr (js_toMutableByteArray val)))
        0
        (js_byteLength val)

fromByteString :: ByteString -> JSVal
fromByteString (BS.PS (ForeignPtr addr _) offset length) =
  js_sliceBuffer addr offset length

exportCallback :: (Callback (JSVal -> IO ())) -> IO ()
exportCallback cb = js_setCallback (jsval cb)

foreign import javascript unsafe
  "$r = $1;"
  js_toMutableByteArray :: JSVal -> MutableByteArray# RealWorld

foreign import javascript unsafe
  "var start = $1_1 ? ($1_2 + $1_1.u8.byteOffset + $2) : 0; $r = $1_1 ? $1_1.u8.buffer.slice(start, start + $3) : null;"
  js_sliceBuffer :: Addr# -> Int -> Int -> JSVal

foreign import javascript unsafe
  "$r1 = $1; $r2 = 0;"
  js_toAddr :: JSVal -> Addr#

foreign import javascript unsafe
  "$r = $1.len;"
  js_byteLength :: JSVal -> Int

foreign import javascript unsafe
  "h$plutusRequestHandler.setCallback($1);"
  js_setCallback :: JSVal -> IO ()

foreign import javascript safe
  "h$plutusRequestHandler.respond($1,$2,$3,$4);"
  js_respond :: Int -> JSVal -> JSVal -> JSVal -> IO ()
