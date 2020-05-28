{-# LANGUAGE TemplateHaskell #-}
module App where

import           Aws.Lambda
import           Control.Concurrent                    (forkOS, killThread, threadDelay)
import           Control.Concurrent.MVar               (MVar, newEmptyMVar, putMVar, readMVar)
import           Control.Exception                     (try)
import           Data.Aeson                            (encode)
import qualified Data.Aeson                            as JSON
import           Data.Bifunctor                        (first)
import           Data.ByteString.Lazy.UTF8             as BSU
import           Data.Proxy                            (Proxy (Proxy))
import           Language.Marlowe                      (Contract (Close), Slot (Slot), State, TransactionInput,
                                                        TransactionWarning)
import           Language.Marlowe.Analysis.FSSemantics (warningsTraceWithState)
import           Language.Marlowe.Pretty
import           Marlowe.Symbolic.Types.API            (API)
import           Marlowe.Symbolic.Types.Request        (Request (Request, callbackUrl, contract, state))
import qualified Marlowe.Symbolic.Types.Request        as Req
import           Marlowe.Symbolic.Types.Response       (Response (Response, result), Result (CounterExample, Error, Valid, initialSlot, transactionList, transactionWarning))
import qualified Marlowe.Symbolic.Types.Response       as Res
import           Network.HTTP.Client                   (newManager)
import           Network.HTTP.Client.TLS               (tlsManagerSettings)
import           Servant.API                           (NoContent)
import           Servant.Client                        (ClientEnv, ClientM, client, mkClientEnv, parseBaseUrl,
                                                        runClientM)
import           System.Process                        (system)
import           Text.PrettyPrint.Leijen               (displayS, renderCompact)

notifyApi :: Proxy API
notifyApi = Proxy

notifyClient :: Response -> ClientM NoContent
notifyClient = client notifyApi

sendRequest :: String -> Response -> IO ()
sendRequest cu resp = do
  baseUrl <- parseBaseUrl cu
  manager <- newManager tlsManagerSettings
  let clientEnv = mkClientEnv manager baseUrl
  res <- runClientM (notifyClient resp) clientEnv
  print res

prettyToString :: Pretty a => a -> String
prettyToString x = (displayS $ renderCompact $ prettyFragment x) ""

makeResponse :: String ->
                Either String (Maybe (Slot, [TransactionInput], [TransactionWarning]))
             -> Response
makeResponse u (Left err) = Response {Res.uuid = u, result = Error (show err)}
makeResponse u (Right res) =
   Response
     { Res.uuid = u
     , result = case res of
                  Nothing -> Valid
                  Just (Slot sn, ti, tw) ->
                     CounterExample
                       { initialSlot = sn
                       , transactionList = prettyToString ti
                       , transactionWarning = prettyToString tw
                       }
     }

handler :: Request -> Context -> IO (Either Response Response)
handler Request {Req.uuid = u, callbackUrl = cu, contract = c, state = st} context =
  do system "killallz3"
     semaphore <- newEmptyMVar
     let contract :: Maybe Contract
         contract = JSON.decode (BSU.fromString c)
     case contract of
        Nothing -> return $ Left (makeResponse u (Left "Can't parse JSON as a contract"))
        Just contract -> do
            let contract = maybe Close id (JSON.decode (BSU.fromString c))
            let
                state :: Maybe State
                state = JSON.decode (BSU.fromString st)
            mainThread <-
              forkOS (do evRes <- warningsTraceWithState contract state
                         forkOS (do threadDelay 1000000 -- Timeout to send HTTP request (1 sec)
                                    putMVar semaphore
                                      (makeResponse u (Left "Response HTTP request timed out")))
                         let resp = makeResponse u (first show evRes)
                         sendRequest cu resp
                         putMVar semaphore resp)
            timerThread <-
              forkOS (do threadDelay 110000000 -- Timeout in microseconds (1 min 50 sec)
                         putMVar semaphore (makeResponse u $ Left "Symbolic evaluation timed out"))
            x <- readMVar semaphore
            killThread mainThread
            killThread timerThread
            system "killallz3"
            return $ Right x

-- we export the main function so that we can use it in a project that does not require template haskell
generateLambdaDispatcher
