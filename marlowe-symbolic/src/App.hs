{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module App where

import           Aws.Lambda
import           Data.Aeson                            (encode)
import qualified Data.Aeson                            as JSON
import           Data.Bifunctor                        (first)
import           Data.ByteString.Lazy.UTF8             as BSU
import           Data.Maybe                            (fromMaybe)
import           Language.Marlowe                      (Contract, Slot (Slot), State, TransactionInput,
                                                        TransactionWarning)
import           Language.Marlowe.Analysis.FSSemantics (warningsTraceCustom)
import           Language.Marlowe.Pretty
import           Marlowe.Symbolic.Types.Request        (Request (Request, callbackUrl, contract, onlyAssertions, state))
import qualified Marlowe.Symbolic.Types.Request        as Req
import           Marlowe.Symbolic.Types.Response       (Response (Response, result), Result (CounterExample, Error, Valid, initialSlot, transactionList, transactionWarning))
import qualified Marlowe.Symbolic.Types.Response       as Res
import           System.Process                        (system)
import           Text.PrettyPrint.Leijen               (displayS, renderCompact)

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

handler :: Request -> Context () -> IO (Either Response Response)
handler Request {Req.uuid = u, onlyAssertions = oa, contract = c, state = st} _ =
  do _ <- system "killallz3"
     let mContract :: Maybe Contract
         mContract = JSON.decode (BSU.fromString c)
     let state :: Maybe State
         state = JSON.decode (BSU.fromString st)
     let onlyAssertions :: Bool
         onlyAssertions = fromMaybe False (JSON.decode (BSU.fromString oa))
     case mContract of
        Nothing -> return $ Left (makeResponse u (Left "Can't parse JSON as a contract"))
        Just contract -> do
            evRes <- warningsTraceCustom onlyAssertions contract state
            let resp = makeResponse u (first show evRes)
            _ <- system "killallz3"
            putStrLn $ BSU.toString $ encode resp
            pure $ Right resp

initializeContext :: IO ()
initializeContext = pure ()

-- we export the main function so that we can use it in a project that does not require template haskell
generateLambdaDispatcher StandaloneLambda $ DispatcherOptions (ApiGatewayDispatcherOptions False)
